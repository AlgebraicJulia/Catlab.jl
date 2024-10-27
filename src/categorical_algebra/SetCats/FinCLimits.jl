module FinCLimits 

using DataStructures, StructEquality, StaticArrays, GATlab

using ACSets: incident, copy_parts!
using GATlab: ThCategory
using .ThCategory

using ...Cats.Limits, ...Cats.FreeDiagrams, ..FinFunctions,  ..FinSets
using ..Sets: AbsSet, TypeSet, SetOb
using ..SetFunctions: SetC, SetFunction, ConstantFunction
using ..FinFunctions: ensure_indexed
using ...Cats.FreeDiagrams: AbsBipartiteFreeDiagram, DiagramImpl, objects
using ...Cats.Limits: LimitAlgorithm, NamedColimit, LimitImpl
import ...Cats.Limits: limit, colimit, _universal, cone, ob
using ....Graphs: edges, src, tgt, add_vertices₁!, add_vertex₁!, vertices₂, nv₁, 
                 nv₂, add_vertices₂!, add_edges!,add_edge!, vertices₁, 
                 rem_vertices₂!, inneighbors, add_vertex₂!, rem_edges!
using ....Theories: ThCocartesianCategory, hom

# Note: Cartesian monoidal structure is implemented generically for Set but
# cocartesian only for FinSet.
@cocartesian_monoidal_instance FinSet FinFunction SetC

# Structs
#########

"""
The normal Default colimit alg will be to check if the diagram is in FinSetInt,
otherwise to use NamedColimits. `DefaultAlg′ is the default alg for FinSetInt
colimits.
"""
@struct_hash_equal struct DefaultAlg′ <: LimitAlgorithm end 

""" Limit of finite sets with a reverse mapping or index into the limit set.

This type provides a fallback for limit algorithms that do not come with a
specialized algorithm to apply the universal property of the limit. In such
cases, you can explicitly construct a mapping from tuples of elements in the
feet of the limit cone to elements in the apex of the cone.

The index is constructed the first time it is needed. Thus there is no extra
cost to using this type if the universal property will not be invoked.
"""
mutable struct FinSetIndexedLimit <: LimitImpl{FinSet, FinDomFunction}
  cone::Multispan
  index::Union{AbstractDict,Nothing}
end

FinSetIndexedLimit(cone::Multispan) = FinSetIndexedLimit(cone, nothing)

cone(l::FinSetIndexedLimit) = l.cone
ob(l::FinSetIndexedLimit) = apex(cone(l))

function make_limit_index(cone::Multispan)
  πs = Tuple(legs(cone))
  index = Dict{Tuple{map(eltype∘codom, πs)...}, eltype(apex(cone))}()
  for x in apex(cone)
    index[map(π -> π(x), πs)] = x
  end
  return index
end

function _universal(::Any, ::SetC, lim::FinSetIndexedLimit, cone::Multispan)
  if isnothing(lim.index)
    lim.index = make_limit_index(lim.cone)
  end
  fs = Tuple(legs(cone))
  FinFunction(Int[lim.index[map(f -> f(x), fs)] for x in apex(cone)],
              ob(lim))
end

""" Limit of finite sets viewed as a table.

Any limit of finite sets can be canonically viewed as a table
([`TabularSet`](@ref)) whose columns are the legs of the limit cone and whose
rows correspond to elements of the limit object. To construct this table from an
already computed limit, call `TabularLimit(::AbstractLimit; ...)`. The column
names of the table are given by the optional argument `names`.

In this tabular form, applying the universal property of the limit is trivial
since it is just tupling. Thus, this representation can be useful when the
original limit algorithm does not support efficient application of the universal
property. On the other hand, this representation has the disadvantage of
generally making the element type of the limit set more complicated.
"""
struct TabularLimit{Ob,Hom} <: LimitImpl{Ob,Hom}
  cone::Multispan
end

function TabularLimit(lim::Limit; names=nothing)
  πs = legs(lim)
  names = isnothing(names) ? (1:length(πs)) : names
  names = Tuple(column_name(name) for name in names)
  table = TabularSet(NamedTuple{names}(Tuple(map(collect, πs))))
  cone = Multispan(table, map(πs, eachindex(πs)) do π, i
    FinFunction(row -> Tables.getcolumn(row, i), table, codom(π))
  end)
  Limit(lim.diagram, cone)
end

function _universal(::Diagram, ::SetC, lim::TabularLimit,cone::Multispan)
  fs = Tuple(legs(cone))
  FinFunction(x -> Row(map(f -> f(x), fs)), apex(cone), ob(lim))
end

column_name(name) = Symbol(name)
column_name(i::Integer) = Symbol("x$i") # Same default as DataFrames.jl.

# Terminal object
#################

limit(e::EmptyDiagram, m::SetC, ::DefaultAlg) =
  Limit(Diagram(e, m), Multispan{SetC}(FinSet(1), FinFunction[]))

_universal(::EmptyDiagram, ::SetC, ::LimitCone, c::Multispan) =
  SetFunction(ConstantFunction(1, apex(c), FinSet(1)))

# Initial object
################

colimit(e::EmptyDiagram, m::SetC, ::DefaultAlg) =
  Colimit(Diagram(e, m), Multicospan{SetC}(FinSet()))

_universal(::EmptyDiagram, ::SetC, ::ColimitCocone, x::Multicospan) =
  FinFunction(Int[], apex(x))
 
# Products
##########

function limit(Xs::DiscreteDiagram, m::SetC, ::DefaultAlg)
  all(X -> X isa FinSet, Xs) || return type_product(Xs)
  ns = length.(Xs)
  indices = CartesianIndices(Tuple(ns))
  n = prod(ns)
  πs = map(1:length(ns)) do j 
    FinFunction([indices[i][j] for i in 1:n], ns[j]) 
  end
  Limit(Diagram(Xs, m), Multispan{SetC}(FinSet(n), πs))
end

function type_product(Xs::DiscreteDiagram{Ob,Hom}) where {Ob,Hom}
  X = TypeSet(Tuple{map(eltype, Xs)...}) |> SetOb
  πs = [ SetFunction(x -> getindex(x, i), X, Xi) for (i, Xi) in enumerate(Xs) ]
  Limit(Diagram(Xs, SetC()), Multispan{Ob,Hom}(X, πs))
end

function _universal(Xs::DiscreteDiagram, ::SetC, res::LimitCone, cone::Multispan)
  all(X -> X isa FinSet, Xs) || return universal_typeset(res, cone)
  ns = length.(codom.(cone))
  indices = LinearIndices(Tuple(ns))
  v = map(apex(cone)) do i 
    indices[(f(i) for f in cone)...]
  end
  FinFunction(v, apex(res))
end

function universal_typeset(lim::LimitCone, span::Multispan)
  @assert length(cone(lim)) == length(span)
  fs = Tuple(legs(span))
  SetFunction(x -> map(f -> f(x), fs), apex(span), ob(lim))
end

# Coproducts
############

""" Coproduct in FinSetInt """
function colimit(Xs::DiscreteDiagram, m::SetC, ::DefaultAlg′)
  ns = length.(Xs)
  n = sum(ns)
  offsets = [0, cumsum(ns)...]
  ιs = map(1:length(ns)) do j 
    FinFunction((1:ns[j]) .+ offsets[j], n) 
  end
  Colimit(Diagram(Xs, m), Multicospan{SetC}(FinSet(n), ιs))
end

function _universal(::DiscreteDiagram, ::SetC, ::ColimitCocone, cocone::Multicospan{Ob,Hom}) where {Ob,Hom}
  cod = apex(cocone)
  FinDomFunction(mapreduce(collect, vcat, cocone, init=Int[]), cod)
end

# Equalizers
############

function limit(para::ParallelMorphisms, c::SetC, ::DefaultAlg)
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m = length(dom(para))
  eq = FinFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m), m)
  Limit(Diagram(para, c), Multispan{SetC}(dom(eq), [eq]))
end

function _universal(::ParallelMorphisms, ::SetC, res::LimitCone, x::Multispan)
  ι = collect(only(cone(res)))
  h = only(x)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], length(ι))
end

# Coequalizers
##############

""" Equalizer in FinSetInt """
function colimit(para::ParallelMorphisms{Ob,Hom}, c::SetC, ::DefaultAlg′) where {Ob,Hom}
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m, n = length(dom(para)), length(codom(para))
  sets = IntDisjointSets(n)
  for i in 1:m
    for f in frest
      union!(sets, f1(i), f(i))
    end
  end
  q = quotient_projection(sets)
  Colimit(Diagram(para, c), Multicospan{Ob,Hom}([q]))
end

function _universal(::ParallelMorphisms, ::SetC, res::ColimitCocone, x::Multicospan)
  pass_to_quotient(only(cocone(res)), only(x))
end

""" Create projection map π: X → X/∼ from partition of X.
"""
function quotient_projection(sets::IntDisjointSets)
  h = [ find_root!(sets, i) for i in 1:length(sets) ]
  roots = unique!(sort(h))
  FinFunction([ searchsortedfirst(roots, r) for r in h ], length(roots))
end

""" Given h: X → Y, pass to quotient q: X/~ → Y under projection π: X → X/~.
"""
function pass_to_quotient(π::FinFunction, h::FinFunction)
  @assert dom(π) == dom(h)
  q = zeros(Int, length(codom(π)))
  for i in dom(h)
    j = π(i)
    if q[j] == 0
      q[j] = h(i)
    else
      q[j] == h(i) || error("Quotient map of colimit is ill-defined")
    end
  end
  any(==(0), q) && error("Projection map is not surjective")
  FinFunction(q, codom(h))
end

function pass_to_quotient(π::FinFunction, h::FinDomFunction)
  @assert dom(π) == dom(h)
  q = Vector{Union{Some{eltype(codom(h))},Nothing}}(nothing, length(codom(π)))
  for i in dom(h)
    j = π(i)
    if isnothing(q[j])
      q[j] = Some(h(i))
    else
      something(q[j]) == h(i) || error("Quotient map of colimit is ill-defined")
    end
  end
  any(isnothing, q) && error("Projection map is not surjective")
  FinDomFunction(map(something, q), codom(h))
end


# Pullbacks 
###########


# Hash Join
#----------

function limit(cospan::Multicospan{Ob, Hom}, m::SetC, ::HashJoin) where {Ob,Hom}
  # We follow the standard terminology for hash joins: in a multiway hash join,
  # one function, called the *probe*, will be iterated over and need not be
  # indexed, whereas the other functions, call *build* inputs, must be indexed.
  #
  # We choose as probe the unindexed function with largest domain. If all
  # functions are already indexed, we arbitrarily choose the first one.
  i = argmax(map(legs(cospan)) do f
    is_indexed(f) ? -1 : length(dom(f))
  end)
  probe = legs(cospan)[i]
  builds = map(ensure_indexed, deleteat(legs(cospan), i))
  πs_build, π_probe = hash_join(builds, probe)
  cone = FinSetIndexedLimit(Multispan{Ob,Hom}(insert(πs_build, i, π_probe)))
  Limit(Diagram(cospan, m), cone)
end

deleteat(vec::Vector, i) = deleteat!(copy(vec), i)
deleteat(vec::StaticVector, i) = StaticArrays.deleteat(vec, i)

insert(vec::Vector{T}, i, x::S) where {T,S} = 
  insert!(collect(typejoin(T,S), vec), i, x)

insert(vec::StaticVector{N,T}, i, x::S) where {N,T,S} =
  StaticArrays.insert(similar_type(vec, typejoin(T,S))(vec), i, x)

function hash_join(builds::AbstractVector, probe::FinDomFunction)
  π_builds, πp = map(_ -> Int[], builds), Int[]
  for y in dom(probe)
    val = probe(y)
    preimages = map(build -> preimage(build, val), builds)
    n_preimages = Tuple(map(length, preimages))
    n = prod(n_preimages)
    if n > 0
      indices = CartesianIndices(n_preimages)
      for j in eachindex(π_builds)
        πb, xs = π_builds[j], preimages[j]
        append!(πb, (xs[I[j]] for I in indices))
      end
      append!(πp, (y for i in 1:n))
    end
  end
  (map(FinFunction, π_builds, map(dom, builds)), FinFunction(πp, dom(probe)))
end

function hash_join(build::FinDomFunction{Int}, probe::FinDomFunction{Int})
  πb, πp = Int[], Int[]
  for y in dom(probe)
    xs = preimage(build, probe(y))
    n = length(xs)
    if n > 0
      append!(πb, xs)
      append!(πp, (y for i in 1:n))
    end
  end
  (FinFunction(πb, dom(build)), FinFunction(πp, dom(probe)))
end

# SortMergeJoin
###############

function limit(cospan::Multicospan{Ob,Hom}, m::SetC, ::SortMergeJoin) where {Ob,Hom}
  funcs = map(collect, legs(cospan))
  sorts = map(sortperm, funcs)
  values = similar_mutable(funcs, eltype(apex(cospan)))
  ranges = similar_mutable(funcs, UnitRange{Int})

  function next_range!(i::Int)
    f, sort = funcs[i], sorts[i]
    n = length(f)
    start = last(ranges[i]) + 1
    ranges[i] = if start <= n
      val = values[i] = f[sort[start]]
      stop = start + 1
      while stop <= n && f[sort[stop]] == val; stop += 1 end
      start:(stop - 1)
    else
      start:n
    end
  end

  πs = map(_ -> Int[], funcs)
  for i in eachindex(ranges)
    ranges[i] = 0:0
    next_range!(i)
  end
  while !any(isempty, ranges)
    if all(==(values[1]), values)
      indices = CartesianIndices(Tuple(ranges))
      for i in eachindex(πs)
        append!(πs[i], (sorts[i][I[i]] for I in indices))
        next_range!(i)
      end
    else
      next_range!(argmin(values))
    end
  end
  cone = Multispan{Ob,Hom}(map((π,f) -> FinFunction(π, length(f)), πs, funcs))
  Limit(Diagram(cospan, m), FinSetIndexedLimit(cone))
end

similar_mutable(x::AbstractVector, T::Type) = similar(x, T)

# NestedLoopJoin
################

"""
A nested-loop join is algorithmically the same as `ComposeProductEqualizer`,
but for completeness and performance we give a direct implementation here.
"""
function limit(cospan::Multicospan{Ob,Hom}, m::SetC, ::NestedLoopJoin) where {Ob,Hom}
  funcs = legs(cospan)
  ns = map(length, feet(cospan))
  πs = map(_ -> Int[], funcs)
  for I in CartesianIndices(Tuple(ns))
    values = map((f, i) -> f(I[i]), funcs, eachindex(funcs))
    if all(==(values[1]), values)
      for i in eachindex(πs)
        push!(πs[i], I[i])
      end
    end
  end
  cone = Multispan{Ob,Hom}(map((π,f) -> FinFunction(π, dom(f)), πs, funcs))
  Limit(Diagram(cospan, m), FinSetIndexedLimit(cone))
end

# Smart Join
############

function limit(cospan::Multicospan{Ob,Hom}, m::SetC, ::SmartJoin) where {Ob,Hom}
  # Handle the important special case where one of the legs is a constant
  # (function out of a singleton set). In this case, we just need to take a
  # product of preimages of the constant value.
  funcs = legs(cospan)
  i = findfirst(f -> length(dom(f)) == 1, funcs)
  if !isnothing(i)
    c = funcs[i](1)
    ιs = map(deleteat(funcs, i)) do f
      FinFunction(preimage(f, c), dom(f))
    end
    x, πs = if length(ιs) == 1
      dom(only(ιs)), ιs
    else
      prod = product(map(dom, ιs))
      ob(prod), map(compose, legs(prod), ιs)
    end
    πs = insert(πs, i, FinDomFunction(ConstantFunction(1, x, FinSet(1))))
    impl = FinSetIndexedLimit(Multispan(x, πs))
    return Limit(Diagram(cospan, m), impl)
  end

  # In the general case, for now we always just do a hash join, although
  # sort-merge joins can sometimes be faster.
  limit(cospan, m, HashJoin())
end

""" Use SmartJoin by default """
limit(cospan::Multicospan{Ob,Hom}, m::SetC, ::DefaultAlg) where {Ob,Hom} = 
  limit(cospan, m, SmartJoin())


# Bipartite diagrams
####################

"""
Bipartite limit via a big product and equalizer
"""
function limit(dia::AbsBipartiteFreeDiagram, m::SetC, ::DefaultAlg)
  prod = product(ob₁(dia), m)
  eq = equalizer(map(edges(dia)) do e
    compose[m](legs(prod)[src(dia, e)], hom(dia, e))
  end, m)
  ι = incl(eq)
  cone = Multispan{SetC}(dom(ι), compose[m].(Ref(ι),legs(prod)))
  Limit(Diagram(dia, m), CompositeLimit(cone, prod, ι))
end

function _universal(::AbsBipartiteFreeDiagram, ::SetC, lim::CompositeLimit, x::Multispan)
  ι = collect(lim.incl)
  h = universal(lim.prod, x)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], apex(lim))
end

function limit(d::AbsBipartiteFreeDiagram{Ob,Hom}, m::SetC) where {Ob,Hom}
  dia = Diagram(d, m)
  # As in a pullback, this method assumes that all objects in layer 2 have
  # incoming morphisms.
  @assert !any(isempty(incident(d, v, :tgt)) for v in vertices₂(d))
  d_original = d
  d′ = BipartiteFreeDiagram{Ob,Hom}()
  add_vertices₁!(d′, nv₁(d), ob₁=ob₁(d))
  add_vertices₂!(d′, nv₂(d), ob₂=ob₂(d))#ensure_type_set.(ob₂(d)))
  add_edges!(d′,src(d,edges(d)),tgt(d,edges(d)),hom=hom(d))#ensure_type_set_codom.(hom(d)))
  d = d′

  # It is generally optimal to compute all equalizers (self joins) first, so as
  # to reduce the sizes of later pullbacks (joins) and products (cross joins).
  d, ιs = equalize_all(d)
  rem_vertices₂!(d, [v for v in vertices₂(d) if
                     length(incident(d, v, :tgt)) == 1])

  # Perform all pairings before computing any joins.
  d = pair_all(d)

  # Having done this preprocessing, if there are any nontrivial joins, perform
  # one of them and recurse; otherwise, we have at most a product to compute.
  #
  # In the binary case (`nv₁(d) == 2`), the preprocessing guarantees that there
  # is at most one nontrivial join, so there are no choices to make. When there
  # are multiple possible joins, do the one with smallest base cardinality
  # (product of sizes of relations to join). This is a simple greedy heuristic.
  # For more control over the order of the joins, create a UWD schedule.
  if nv₂(d) == 0
    # FIXME: Shouldn't need FinSetIndexedLimit in these special cases.
    if nv₁(d) == 1
      Limit(dia, FinSetIndexedLimit(Multispan(dom(ιs[1]), [ιs[1]])))
    else
      πs = legs(product(ob₁(d), m))
      ls = Multispan{Ob,Hom}(map(compose[m], πs, ιs))
      Limit(dia, FinSetIndexedLimit(ls))
    end
  else
    # Select the join to perform.
    v = argmin(map(vertices₂(d)) do v
      edges = incident(d, v, :tgt)
      @assert length(edges) >= 2
      prod(e -> length(dom(hom(d, e))), edges)
    end)

    # Compute the pullback (inner join).
    join_edges = incident(d, v, :tgt)
    to_join = src(d, join_edges)
    to_keep = setdiff(vertices₁(d), to_join)
    pb = pullback(hom(d, join_edges), m, alg=SmartJoin())

    # Create a new bipartite diagram with joined vertices.
    d_joined = BipartiteFreeDiagram{Ob,Hom}()
    copy_parts!(d_joined, d, V₁=to_keep, V₂=setdiff(vertices₂(d),v), E=edges(d))
    joined = add_vertex₁!(d_joined, ob₁=apex(pb))
    for (u, π) in zip(to_join, legs(pb))
      for e in setdiff(incident(d, u, :src), join_edges)
        set_subparts!(d_joined, e, src=joined, hom=π⋅hom(d,e))
      end
    end
    rem_edges!(d_joined, join_edges)

    # Recursively compute the limit of the new diagram.
    lim = limit(d_joined, m)

    # Assemble limit cone from cones for pullback and reduced limit.
    πs = Vector{FinDomFunction}(undef, nv₁(d))
    for (i, u) in enumerate(to_join)
      πs[u] = compose[m](last(legs(lim)), compose[m](legs(pb)[i], ιs[u]))
    end
    for (i, u) in enumerate(to_keep)
      πs[u] = compose[m](legs(lim)[i], ιs[u])
    end
    Limit(dia,FinSetIndexedLimit(Multispan{Ob,Hom}(πs)))
  end
end

# ensure_type_set(s::FinSet) = TypeSet(eltype(s))
# ensure_type_set(s::TypeSet) = s
# ensure_type_set_codom(f::FinFunction) =
#   FinDomFunction(collect(f),dom(f), TypeSet(eltype(codom(f))))
# ensure_type_set_codom(f::IndexedFinFunctionVector) =
#   IndexedFinDomFunctionVector(f.func, index=f.index)
# ensure_type_set_codom(f::FinDomFunction) = f

""" Compute all possible equalizers in a bipartite free diagram.

The result is a new bipartite free diagram that has the same vertices but is
*simple*, i.e., has no multiple edges. The list of inclusion morphisms into
layer 1 of the original diagram is also returned.
"""
function equalize_all(d::AbsBipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom}
  d_simple = BipartiteFreeDiagram{Ob,Hom}()
  copy_parts!(d_simple, d, V₂=vertices₂(d))
  ιs = map(vertices₁(d)) do u
    # Collect outgoing edges of u, key-ed by target vertex.
    out_edges = OrderedDict{Int,Vector{Int}}()
    for e in incident(d, u, :src)
      push!(get!(out_edges, tgt(d,e)) do; Int[] end, e)
    end

    # Equalize all sets of parallel edges out of u.
    ι = id[SetC()](ob₁(d, u))
    for es in values(out_edges)
      if length(es) > 1
        fs = [compose[SetC()](ι,f) for f in hom(d, es)]
        ι = compose[SetC()](incl(equalizer(fs, SetC())), ι)
      end
    end

    add_vertex₁!(d_simple, ob₁=dom(ι)) # == u
    for (v, es) in pairs(out_edges)
      add_edge!(d_simple, u, v, hom=compose[SetC()](ι,hom(d, first(es))))
    end
    ι
  end
  (d_simple, ιs)
end

""" Perform all possible pairings in a bipartite free diagram.

The resulting diagram has the same layer 1 vertices but a possibly reduced set
of layer 2 vertices. Layer 2 vertices are merged when they have exactly the same
multiset of adjacent vertices.
"""
function pair_all(d::AbsBipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom}
  d_paired = BipartiteFreeDiagram{Ob,Hom}()
  copy_parts!(d_paired, d, V₁=vertices₁(d))

  # Construct mapping to V₂ vertices from multisets of adjacent V₁ vertices.
  outmap = OrderedDict{Vector{Int},Vector{Int}}()
  for v in vertices₂(d)
    push!(get!(outmap, sort(inneighbors(d, v))) do; Int[] end, v)
  end

  for (srcs, tgts) in pairs(outmap)
    in_edges = map(tgts) do v
      sort(incident(d, v, :tgt), by=e->src(d,e))
    end
    if length(tgts) == 1
      v = add_vertex₂!(d_paired, ob₂=ob₂(d, only(tgts)))
      add_edges!(d_paired, srcs, fill(v, length(srcs)),
                 hom=hom(d, only(in_edges)))
    else
      prod = product(ob₂(d, tgts), SetC())
      v = add_vertex₂!(d_paired, ob₂=ob(prod))
      for (i,u) in enumerate(srcs)
        f = pair(prod, hom(d, getindex.(in_edges, i)))
        add_edge!(d_paired, u, v, hom=f)
      end
    end
  end
  d_paired
end


"""
Uses the general formula for limits in Set (Leinster, 2014, Basic Category
Theory, Example 5.1.22 / Equation 5.16). This method is simple and direct,
but extremely inefficient!
"""
function limit(F::FreeDiagram, m::SetC, ::DefaultAlg)
  prod = product(ob(F), m)
  n, πs = length(ob(prod)), legs(prod)
  ι = FinFunction(filter(1:n) do i
    all(edges(F)) do e
      s, t, h = src(F, e), tgt(F, e), hom(F, e)
      h(πs[s](i)) == πs[t](i)
    end
  end, n)
  cone = Multispan(dom(ι), map(π -> compose[m](ι,π), πs))
  Limit(Diagram(F, m), CompositeLimit(cone, prod, ι))
end


function _universal(::FreeDiagram, ::SetC, lim::CompositeLimit, cone::Multispan)
  ι = collect(lim.incl)
  h = universal(lim.prod, cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)],
              ob(lim))
end


colimit(span::Multispan, m::SetC, ::DefaultAlg′) = 
  colimit(span, m, ComposeCoproductCoequalizer())

"""
Colimit in FinSetInt.

As in a pushout, this method assume that all objects in layer 1 have
outgoing morphisms so that they can be excluded from the coproduct.
"""
function colimit(d::AbsBipartiteFreeDiagram, m::SetC, ::DefaultAlg′)
  @assert !any(isempty(incident(d, u, :src)) for u in vertices₁(d))
  coprod = coproduct(ob₂(d), m)
  n, ιs = length(ob(coprod)), legs(coprod)
  sets = IntDisjointSets(n)
  for u in vertices₁(d)
    out_edges = incident(d, u, :src)
    for (e1, e2) in zip(out_edges[1:end-1], out_edges[2:end])
      h1, h2 = hom(d, e1), hom(d, e2)
      ι1, ι2 = ιs[tgt(d, e1)], ιs[tgt(d, e2)]
      for i in ob₁(d, u)
        union!(sets, ι1(h1(i)), ι2(h2(i)))
      end
    end
  end
  π = quotient_projection(sets)
  cocone = Multicospan(codom(π), [compose[m](ιs[i],π) for i in vertices₂(d) ])
  Colimit(Diagram(d, m), CompositeColimit(cocone, coprod, π))
end

""" 
Colimit in FinSetInt. Uses the general formula for colimits in Set 
(Leinster, 2014, Basic Category Theory, Example 5.2.16).
"""
function colimit(F::FreeDiagram{Ob,Hom}, m::SetC, ::DefaultAlg′) where {Ob,Hom}
  coprod = coproduct(ob(F), m)
  n, ιs = length(ob(coprod)), legs(coprod)
  sets = IntDisjointSets(n)
  for e in edges(F)
    s, t, h = src(F, e), tgt(F, e), hom(F, e)
    for i in dom(h)
      union!(sets, ιs[s](i), ιs[t](h(i)))
    end
  end
  π = quotient_projection(sets)
  cocone = Multicospan{Ob,Hom}(map(ι -> compose[m](ι,π), ιs))
  Colimit(Diagram(F, m),CompositeColimit(cocone, coprod, π))
end

function _universal(::FreeDiagram, ::SetC, colim::CompositeColimit, cocone::Multicospan)
  h = universal(colim.coprod, cocone)
  pass_to_quotient(colim.proj, h)
end


# Colimits with names
#--------------------

"""
If the diagram is in skeleton of FinSet, use `DefaultAlg′`. Otherwise, used 
`NamedColimit` algorithm which is only defined for BipartiteFreeDiagrams
Reducing to the case of bipartite free diagrams is a bit lazy, but at least
using `specialize` below should avoid some gross inefficiencies.
"""
function colimit(d::DiagramImpl{Ob,Hom}, m::SetC, ::DefaultAlg) where {Ob,Hom}
  is_diag_finsetint(d) && return colimit(d, m, DefaultAlg′())
  colimit(BipartiteFreeDiagram{Ob,Hom}(d), m, NamedColimit())
end 

""" Every object in the diagram is a FinSetInt """
is_diag_finsetint(d::DiagramImpl{Ob,Hom}) where {Ob,Hom} = 
  all(x-> getvalue(x) isa FinSetInt, objects(d))

""" 
Compute colimit of diagram in the skeleton of FinSet (`FinSet{Int}`).
Note: no performance would be gained by using `DisjointSets{T}` from
DataStructures.jl because it is just a wrapper around `IntDisjointSets` that
internally builds the very same indices that we use below.
"""
function colimit(d::BipartiteFreeDiagram{Ob,Hom}, m::SetC, ::NamedColimit) where {Ob,Hom}
  sets₁_skel = map(set -> skeletize(set, index=false), ob₁(d))
  sets₂_skel = map(set -> skeletize(set, index=true), ob₂(d))
  funcs = map(edges(d)) do e
    skeletize(hom(d,e), sets₁_skel[src(d,e)], sets₂_skel[tgt(d,e)])
  end
  d_skel = BipartiteFreeDiagram{FinSet,FinDomFunction}()
  add_vertices₁!(d_skel, nv₁(d), ob₁=dom.(sets₁_skel))
  add_vertices₂!(d_skel, nv₂(d), ob₂=dom.(sets₂_skel))
  add_edges!(d_skel, src(d), tgt(d), hom=funcs)

  # PROBLEM: if we `specialize` here, it changes the # of legs of the colimit!
  # But computing `ιs` requires bijection between `colim_skel` and `sets₂_skel`
  # We want to `specialize` to make the colimit more efficient, though.
  colim_skel = colimit(d_skel, m, DefaultAlg′())

  # Assign elements/names to the colimit set.
  elems = Vector{Symbol}(undef, length(apex(colim_skel)))
  for (ι, Y) in zip(colim_skel, sets₂_skel)
    for i in dom(Y)
      elems[ι(i)] = Y(i)
    end
  end
  # The vector should already be filled, but to reduce arbitrariness we prefer
  # names from the layer 1 sets whenever possible. For example, when computing a
  # pushout, we prefer names from the apex of cospan to names from the feet.
  for (u, X) in zip(vertices₁(d_skel), sets₁_skel)
    e = first(incident(d_skel, u, :src))
    f, ι = hom(d_skel, e), legs(colim_skel)[tgt(d_skel, e)]
    for i in dom(X)
      elems[ι(f(i))] = X(i)
    end
  end
  # Eliminate clashes in provisional list of names.
  unique_by_tagging!(elems)
  ιs = map(colim_skel, sets₂_skel) do ι, Y
    FinFunction(Dict(Y(i) => elems[ι(i)] for i in dom(Y)), FinSet(Set(elems)))
  end
  Colimit(Diagram(d, m), Multicospan{Ob,Hom}(FinSet(Set(elems)), ιs))
end

function skeletize(set::FinSet; index::Bool=false)
  # FIXME: We should support `unique_index` and it should be used here.
  FinDomFunction(collect(set), set, index=index)
end
function skeletize(f::FinFunction, X, Y)
  FinFunction(i -> only(preimage(Y, f(X(i)))), dom(X), dom(Y))
end

""" Make list of elements unique by adding tags if necessary.

If the elements are already unique, they will not be mutated.
"""
function unique_by_tagging!(elems::AbstractVector{T}; tag=default_tag) where T
  tag_count = Dict{T,Int}()
  for x in elems
    tag_count[x] = haskey(tag_count, x) ? 1 : 0
  end
  for (i, x) in enumerate(elems)
    (j = tag_count[x]) > 0 || continue
    tagged = tag(x, j)
    @assert !haskey(tag_count, tagged) # Don't conflict with original elems!
    elems[i] = tagged
    tag_count[x] += 1
  end
  elems
end

default_tag(x::Symbol, t) = Symbol(x, "#", t)
default_tag(x::AbstractString, t) = string(x, "#", t)

end # module
