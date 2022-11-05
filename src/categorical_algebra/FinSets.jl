""" The category of finite sets and functions, and its skeleton.
"""
module FinSets
export FinSet, FinSetCollection, FinSetInt, FinFunction, FinDomFunction,
  force, is_indexed, preimage,
  JoinAlgorithm, SmartJoin, NestedLoopJoin, SortMergeJoin, HashJoin,
  SubFinSet, SubOpBoolean, is_monic, is_epic

using StructEquality
using DataStructures: OrderedDict, IntDisjointSets, union!, find_root!
using Reexport
import StaticArrays
using StaticArrays: StaticVector, SVector, SizedVector, similar_type

@reexport using ..Sets
using ...GAT, ...Theories, ...CSetDataStructures, ...Graphs, ...Columns
using ..FinCats, ..FreeDiagrams, ..Limits, ..Subobjects
import ...Theories: Ob, meet, ∧, join, ∨, top, ⊤, bottom, ⊥
import ..Categories: ob, hom, dom, codom, compose, id, ob_map, hom_map
import ..FinCats: force, ob_generators, hom_generators, ob_generator,
  ob_generator_name, graph, is_discrete
using ..FinCats: dicttype
import ..Limits: limit, colimit, universal
import ..Subobjects: Subobject
using ..Sets: IdentityFunction, SetFunctionCallable

# Finite sets
#############

""" Abstract type for a finite set with elements of type `T`.
"""
abstract type FinSet{T} <: SetOb{T} end

FinSet(set::FinSet) = set

""" Finite set backed by a collection.

In the type `FinSetCollection{S,T}`, the second type parameter `T` is the
element type of the set and the first parameter `S` is the collection type,
which can be a subtype of `AbstractSet` or another Julia collection type.
"""
@struct_hash_equal struct FinSetCollection{S,T} <: FinSet{T}
  collection::S
end

""" Finite set of the form ``{1,…,n}``.

These are the objects of the skeleton of the category **FinSet**, an important
special case implemented as `FinSetCollection{S}` for `S = Base.OneTo`.
"""
const FinSetInt = FinSetCollection{Base.OneTo,Int}

FinSet(n::Int) = FinSetCollection{Base.OneTo, Int}(Base.OneTo(n))
FinSet(collection::S) where {T, S<:Union{AbstractVector{T},AbstractSet{T}}} =
  FinSetCollection{S,T}(collection)

Base.iterate(set::FinSetCollection, args...) = iterate(set.collection, args...)
Base.length(set::FinSetCollection) = length(set.collection)
Base.in(set::FinSetCollection, elem) = in(elem, set.collection)

function Base.show(io::IO, set::FinSetCollection)
  print(io, "FinSet(")
  show(io, set.collection)
  print(io, ")")
end

# Discrete categories
#--------------------

""" Discrete category on a finite set.

The only morphisms in a discrete category are the identities, which are here
identified with the objects.
"""
@struct_hash_equal struct DiscreteCat{Ob,S<:FinSet{Ob}} <: FinCat{Ob,Ob}
  set::S
end
DiscreteCat(n::Integer) = DiscreteCat(FinSet(n))

FinCat(s::Union{FinSet,Integer}) = DiscreteCat(s)

ob_generators(C::DiscreteCat) = C.set
hom_generators(::DiscreteCat) = ()
ob_generator(C::DiscreteCat, x) = x ∈ C.set ? x : error("$x ∉ $(C.set)")
ob_generator_name(C::DiscreteCat, x) = x
hom(C::DiscreteCat, x) = ob_generator(C, x)

is_discrete(::DiscreteCat) = true
graph(C::DiscreteCat{Int,FinSetInt}) = Graph(length(C.set))

dom(C::DiscreteCat{T}, f) where T = f::T
codom(C::DiscreteCat{T}, f) where T = f::T
id(C::DiscreteCat{T}, x) where T = x::T
compose(C::DiscreteCat{T}, f, g) where T = (f::T == g::T) ? f :
  error("Nontrivial composite in discrete category: $f != $g")

hom_map(F::FinDomFunctor{<:DiscreteCat}, x) = id(codom(F), ob_map(F, x))

Base.show(io::IO, C::DiscreteCat{Int,FinSetInt}) =
  print(io, "FinCat($(length(C.set)))")

# Finite functions
##################

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explictly by a vector of integers. In the vector
representation, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented
by the vector [1,3,2,3].

This type is mildly generalized by [`FinDomFunction`](@ref).
"""
const FinFunction{S, S′, Dom <: FinSet{S}, Codom <: FinSet{S′}} =
  SetFunction{Dom,Codom}

FinFunction(f::Function, dom, codom) =
  SetFunctionCallable(f, FinSet(dom), FinSet(codom))
FinFunction(::typeof(identity), args...) =
  IdentityFunction((FinSet(arg) for arg in args)...)
FinFunction(f::AbstractDict, args...) =
  FinFunctionDict(f, (FinSet(arg) for arg in args)...)

function FinFunction(f::AbstractVector{Int}, args...; index=false)
  if index == false
    FinDomFunctionVector(f, (FinSet(arg) for arg in args)...)
  else
    index = index == true ? nothing : index
    IndexedFinFunctionVector(f, args...; index=index)
  end
end
FinFunction(f::AbstractVector{Int}; kw...) =
  FinFunction(f, FinSet(isempty(f) ? 0 : maximum(f)); kw...)

Sets.show_type_constructor(io::IO, ::Type{<:FinFunction}) =
  print(io, "FinFunction")

""" Function out of a finite set.

This class of functions is convenient because it is exactly the class that can
be represented explicitly by a vector of values from the codomain.
"""
const FinDomFunction{S, Dom<:FinSet{S}, Codom<:SetOb} = SetFunction{Dom,Codom}

FinDomFunction(f::Function, dom, codom) =
  SetFunctionCallable(f, FinSet(dom), codom)
FinDomFunction(::typeof(identity), args...) =
  IdentityFunction((FinSet(arg) for arg in args)...)
FinDomFunction(f::AbstractDict, args...) = FinDomFunctionDict(f, args...)

function FinDomFunction(f::AbstractVector, args...; index=false)
  if index == false
    FinDomFunctionVector(f, args...)
  else
    index = index == true ? nothing : index
    IndexedFinDomFunctionVector(f, args...; index=index)
  end
end

Sets.show_type_constructor(io::IO, ::Type{<:FinDomFunction}) =
  print(io, "FinDomFunction")

# Note: Cartesian monoidal structure is implemented generically for Set but
# cocartesian only for FinSet.
@cocartesian_monoidal_instance FinSet FinFunction

Ob(C::FinCat{Int}) = FinSet(length(ob_generators(C)))
Ob(F::Functor{<:FinCat{Int}}) = FinDomFunction(collect_ob(F), Ob(codom(F)))

# Vector-based functions
#-----------------------

""" Function in **Set** represented by a [`Column`](@ref).
"""
struct FinDomFunctionColumn{T,T′,Col<:Column{T,T′}, Dom<:FinSet{T}, Codom<:SetOb{T′}} <:
    SetFunction{Dom,Codom}
  col::Col
  dom::Dom
  codom::Codom
end

(f::FinDomFunctionColumn)(x) = f.col[x]

function Base.show(io::IO, f::FinDomFunctionColumn)
  print(io, "FinDomFunction($(f.col), ")
  Sets.show_domains(io, f)
  print(io, ")")
end

#force(f::FinDomFunction{Int}) = FinDomFunctionVector(map(f, dom(f)), codom(f))
#force(f::FinDomFunctionVector) = f

#Base.collect(f::SetFunction) = force(f).func

""" Function in **FinSet** represented explicitly by a column.
"""
const FinFunctionColumn{T,T′,Col<:Column{T,T′}, Dom<:FinSet{T}, Codom<:FinSet{T′}} =
  FinDomFunctionColumn{T,T′,Col,Dom,Codom}

Base.show(io::IO, f::FinFunctionColumn) =
  print(io, "FinFunction($(f.col), $(length(dom(f))), $(length(codom(f))))")

Sets.do_compose(f::FinFunctionVector, g::FinDomFunctionVector) =
  FinDomFunctionVector(g.func[f.func], codom(g))

""" Whether the given function is indexed, i.e., supports efficient preimages.
"""
is_indexed(::SetFunction) = false
is_indexed(::IdentityFunction) = true
is_indexed(f::FinDomFunctionColumn) = is_indexed(f.col)

""" The preimage (inverse image) of the value y in the codomain.
"""
preimage(f::IdentityFunction, y) = SVector(y)
preimage(f::FinDomFunctionColumn, y) = preimage(f.col, y)

# Forcing
#########

""" Default column type when constructing/forcing functions out of finite sets.
"""
default_column(X::S, X′::S′; kw...) where {S<:SetOb, S′<:SetOb} =
  default_column(S, S′; kw...)

default_column(::Type{<:SetOb{T}}, ::Type{<:SetOb{T′}}; index::Bool=false) where {T, T′} =
  index ? SparseAttrIndexed{T,T′} : SparseAttr{T,T′}

default_column(::Type{FinSetInt}, ::Type{<:SetOb{T}}; index::Bool=false) where {T} =
  index ? DenseAttrIndexed{T} : DenseAttr{T}

default_column(::Type{FinSetInt}, ::Type{FinSetInt}; index::Bool=false) =
  index ? DenseHomIndexed : DenseHom

force(::FinDomFunctionColumn)

# Limits
########

limit(Xs::EmptyDiagram{<:FinSet{Int}}) = Limit(Xs, SMultispan{0}(FinSet(1)))

universal(lim::Limit{<:FinSet{Int},<:EmptyDiagram}, cone::SMultispan{0}) =
  ConstantFunction(1, apex(cone), FinSet(1))

limit(Xs::SingletonDiagram{<:FinSet{Int}}) = limit(Xs, SpecializeLimit())

function limit(Xs::ObjectPair{<:FinSet{Int}})
  m, n = length.(Xs)
  indices = CartesianIndices((m, n))
  π1 = FinFunction(i -> indices[i][1], m*n, m)
  π2 = FinFunction(i -> indices[i][2], m*n, n)
  Limit(Xs, Span(π1, π2))
end

function universal(lim::Limit{<:FinSet{Int},<:ObjectPair}, cone::Span)
  f, g = cone
  m, n = length.(codom.(cone))
  indices = LinearIndices((m, n))
  FinFunction(i -> indices[f(i),g(i)], apex(cone), ob(lim))
end

function limit(Xs::DiscreteDiagram{<:FinSet{Int}})
  ns = length.(Xs)
  indices = CartesianIndices(Tuple(ns))
  n = prod(ns)
  πs = [FinFunction(i -> indices[i][j], n, ns[j]) for j in 1:length(ns)]
  Limit(Xs, Multispan(FinSet(n), πs))
end

function universal(lim::Limit{<:FinSet{Int},<:DiscreteDiagram}, cone::Multispan)
  ns = length.(codom.(cone))
  indices = LinearIndices(Tuple(ns))
  FinFunction(i -> indices[(f(i) for f in cone)...], apex(cone), ob(lim))
end

function limit(pair::ParallelPair{<:FinSet{Int}})
  f, g = pair
  m = length(dom(pair))
  eq = FinFunction(filter(i -> f(i) == g(i), 1:m), m)
  Limit(pair, SMultispan{1}(eq))
end

function limit(para::ParallelMorphisms{<:FinSet{Int}})
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m = length(dom(para))
  eq = FinFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m), m)
  Limit(para, SMultispan{1}(eq))
end

function universal(lim::Limit{<:FinSet{Int},<:ParallelMorphisms},
                   cone::SMultispan{1})
  ι = collect(incl(lim))
  h = only(cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], length(ι))
end

""" Limit of finite sets with a reverse mapping or index into the limit set.

This type provides a fallback for limit algorithms that do not come with a
specialized algorithm to apply the universal property of the limit. In such
cases, you can explicitly construct a mapping from tuples of elements in the
feet of the limit cone to elements in the apex of the cone.

The index is constructed the first time it is needed. Thus there is no extra
cost to using this type if the universal property will not be invoked.
"""
mutable struct FinSetIndexedLimit{Ob<:FinSet,Diagram,Cone<:Multispan{Ob}} <:
    AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  index::Union{AbstractDict,Nothing}
end
FinSetIndexedLimit(diagram, cone::Multispan) =
  FinSetIndexedLimit(diagram, cone, nothing)

function make_limit_index(cone::Multispan{<:FinSet})
  πs = Tuple(legs(cone))
  index = Dict{Tuple{map(eltype∘codom, πs)...}, eltype(apex(cone))}()
  for x in apex(cone)
    index[map(π -> π(x), πs)] = x
  end
  return index
end

function universal(lim::FinSetIndexedLimit, cone::Multispan)
  if isnothing(lim.index)
    lim.index = make_limit_index(lim.cone)
  end
  fs = Tuple(legs(cone))
  FinFunction(Int[lim.index[map(f -> f(x), fs)] for x in apex(cone)],
              apex(cone), ob(lim))
end

""" Algorithm for limit of cospan or multicospan with feet being finite sets.

In the context of relational databases, such limits are called *joins*. The
trivial join algorithm is [`NestedLoopJoin`](@ref), which is algorithmically
equivalent to the generic algorithm `ComposeProductEqualizer`. The algorithms
[`HashJoin`](@ref) and [`SortMergeJoin`](@ref) are usually much faster. If you
are unsure what algorithm to pick, use [`SmartJoin`](@ref).
"""
abstract type JoinAlgorithm <: LimitAlgorithm end

""" Meta-algorithm for joins that attempts to pick an appropriate algorithm.
"""
struct SmartJoin <: JoinAlgorithm end

function limit(cospan::Multicospan{<:SetOb,<:FinDomFunction{Int}};
               alg::LimitAlgorithm=ComposeProductEqualizer())
  limit(cospan, alg)
end

function limit(cospan::Multicospan{<:SetOb,<:FinDomFunction{Int}}, ::SmartJoin)
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
    πs = insert(πs, i, ConstantFunction(1, x, FinSet(1)))
    return FinSetIndexedLimit(cospan, Multispan(πs))
  end

  # In the general case, for now we always just do a hash join, although
  # sort-merge joins can sometimes be faster.
  limit(cospan, HashJoin())
end

deleteat(vec::StaticVector, i) = StaticArrays.deleteat(vec, i)
deleteat(vec::Vector, i) = deleteat!(copy(vec), i)

insert(vec::StaticVector{N,T}, i, x::S) where {N,T,S} =
  StaticArrays.insert(similar_type(vec, typejoin(T,S))(vec), i, x)
insert(vec::Vector{T}, i, x::S) where {T,S} =
  insert!(collect(typejoin(T,S), vec), i, x)

""" [Nested-loop join](https://en.wikipedia.org/wiki/Nested_loop_join) algorithm.

This is the naive algorithm for computing joins.
"""
struct NestedLoopJoin <: JoinAlgorithm end

function limit(cospan::Multicospan{<:SetOb,<:FinDomFunction{Int}},
               ::NestedLoopJoin)
  # A nested-loop join is algorithmically the same as `ComposeProductEqualizer`,
  # but for completeness and performance we give a direct implementation here.
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
  cone = Multispan(map((π,f) -> FinFunction(π, dom(f)), πs, funcs))
  FinSetIndexedLimit(cospan, cone)
end

""" [Sort-merge join](https://en.wikipedia.org/wiki/Sort-merge_join) algorithm.
"""
struct SortMergeJoin <: JoinAlgorithm end

function limit(cospan::Multicospan{<:SetOb,<:FinDomFunction{Int}},
               ::SortMergeJoin)
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
  cone = Multispan(map((π,f) -> FinFunction(π, length(f)), πs, funcs))
  FinSetIndexedLimit(cospan, cone)
end

similar_mutable(x::AbstractVector, T::Type) = similar(x, T)

function similar_mutable(x::StaticVector{N}, T::Type) where N
  # `similar` always returns an `MVector` but `setindex!(::MVector, args...)`
  # only works when the element type is a bits-type.
  isbitstype(T) ? similar(x, T) : SizedVector{N}(Vector{T}(undef, N))
end

""" [Hash join](https://en.wikipedia.org/wiki/Hash_join) algorithm.
"""
struct HashJoin <: JoinAlgorithm end

function limit(cospan::Multicospan{<:SetOb,<:FinDomFunction{Int}}, ::HashJoin)
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
  FinSetIndexedLimit(cospan, Multispan(insert(πs_build, i, π_probe)))
end

function hash_join(builds::AbstractVector{<:FinDomFunction{Int}},
                   probe::FinDomFunction{Int})
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

function hash_join(builds::StaticVector{1,<:FinDomFunction{Int}},
                   probe::FinDomFunction{Int})
  πb, πp = hash_join(builds[1], probe)
  (SVector((πb,)), πp)
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

ensure_indexed(f::FinFunction{Int,Int}) = is_indexed(f) ? f :
  FinFunction(collect(f), codom(f), index=true)
ensure_indexed(f::FinDomFunction{Int}) = is_indexed(f) ? f :
  FinDomFunction(collect(f), index=true)

function limit(d::BipartiteFreeDiagram{<:SetOb,<:FinDomFunction{Int}})
  # As in a pullback, this method assumes that all objects in layer 2 have
  # incoming morphisms.
  @assert !any(isempty(incident(d, v, :tgt)) for v in vertices₂(d))
  d_original = d

  # For uniformity, e.g. when pairing below, ensure that all objects in layer 2
  # are type sets.
  if !all(x isa TypeSet for x in ob₂(d))
    d = map(d, ob₁=identity, ob₂=ensure_type_set, hom=ensure_type_set_codom)
  end

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
      FinSetIndexedLimit(d_original, SMultispan{1}(ιs[1]))
    else
      πs = legs(product(SVector(ob₁(d)...)))
      FinSetIndexedLimit(d_original, Multispan(map(compose, πs, ιs)))
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
    pb = pullback(SVector(hom(d, join_edges)...), alg=SmartJoin())

    # Create a new bipartite diagram with joined vertices.
    d_joined = BipartiteFreeDiagram{SetOb,FinDomFunction{Int}}()
    copy_parts!(d_joined, d, V₁=to_keep, V₂=setdiff(vertices₂(d),v), E=edges(d))
    joined = add_vertex₁!(d_joined, ob₁=apex(pb))
    for (u, π) in zip(to_join, legs(pb))
      for e in setdiff(incident(d, u, :src), join_edges)
        set_subparts!(d_joined, e, src=joined, hom=π⋅hom(d,e))
      end
    end
    rem_edges!(d_joined, join_edges)

    # Recursively compute the limit of the new diagram.
    lim = limit(d_joined)

    # Assemble limit cone from cones for pullback and reduced limit.
    πs = Vector{FinDomFunction{Int}}(undef, nv₁(d))
    for (i, u) in enumerate(to_join)
      πs[u] = compose(last(legs(lim)), legs(pb)[i], ιs[u])
    end
    for (i, u) in enumerate(to_keep)
      πs[u] = compose(legs(lim)[i], ιs[u])
    end
    FinSetIndexedLimit(d_original, Multispan(πs))
  end
end

ensure_type_set(s::FinSet) = TypeSet(eltype(s))
ensure_type_set(s::TypeSet) = s
ensure_type_set_codom(f::FinFunction) =
  SetFunctionCallable(f, dom(f), TypeSet(eltype(codom(f))))
ensure_type_set_codom(f::IndexedFinFunctionVector) =
  IndexedFinDomFunctionVector(f.func, index=f.index)
ensure_type_set_codom(f::FinDomFunction) = f

""" Compute all possible equalizers in a bipartite free diagram.

The result is a new bipartite free diagram that has the same vertices but is
*simple*, i.e., has no multiple edges. The list of inclusion morphisms into
layer 1 of the original diagram is also returned.
"""
function equalize_all(d::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom}
  d_simple = BipartiteFreeDiagram{Ob,Hom}()
  copy_parts!(d_simple, d, V₂=vertices₂(d))
  ιs = map(vertices₁(d)) do u
    # Collect outgoing edges of u, key-ed by target vertex.
    out_edges = OrderedDict{Int,Vector{Int}}()
    for e in incident(d, u, :src)
      push!(get!(out_edges, tgt(d,e)) do; Int[] end, e)
    end

    # Equalize all sets of parallel edges out of u.
    ι = id(ob₁(d, u))
    for es in values(out_edges)
      if length(es) > 1
        fs = SVector((ι⋅f for f in hom(d, es))...)
        ι = incl(equalizer(fs)) ⋅ ι
      end
    end

    add_vertex₁!(d_simple, ob₁=dom(ι)) # == u
    for (v, es) in pairs(out_edges)
      add_edge!(d_simple, u, v, hom=ι⋅hom(d, first(es)))
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
function pair_all(d::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom}
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
      prod = product(SVector(ob₂(d, tgts)...))
      v = add_vertex₂!(d_paired, ob₂=ob(prod))
      for (i,u) in enumerate(srcs)
        f = pair(prod, hom(d, getindex.(in_edges, i)))
        add_edge!(d_paired, u, v, hom=f)
      end
    end
  end
  d_paired
end

""" Limit of general diagram of FinSets computed by product-then-filter.

See `Limits.CompositePullback` for a very similar construction.
"""
struct FinSetCompositeLimit{Ob<:FinSet, Diagram,
                            Cone<:Multispan{Ob}, Prod<:Product{Ob},
                            Incl<:FinFunction} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  prod::Prod
  incl::Incl # Inclusion for the "multi-equalizer" in general formula.
end

limit(d::FreeDiagram{<:FinSet{Int}}) = limit(FinDomFunctor(d))

function limit(F::Functor{<:FinCat{Int},<:TypeCat{<:FinSet{Int}}})
  # Uses the general formula for limits in Set (Leinster, 2014, Basic Category
  # Theory, Example 5.1.22 / Equation 5.16). This method is simple and direct,
  # but extremely inefficient!
  J = dom(F)
  prod = product(map(x -> ob_map(F, x), ob_generators(J)))
  n, πs = length(ob(prod)), legs(prod)
  ι = FinFunction(filter(1:n) do i
    all(hom_generators(J)) do f
      s, t, h = dom(J, f), codom(J, f), hom_map(F, f)
      h(πs[s](i)) == πs[t](i)
    end
  end, n)
  cone = Multispan(dom(ι), map(x -> ι⋅πs[x], ob_generators(J)))
  FinSetCompositeLimit(F, cone, prod, ι)
end

function universal(lim::FinSetCompositeLimit, cone::Multispan{<:FinSet{Int}})
  ι = collect(lim.incl)
  h = universal(lim.prod, cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)],
              apex(cone), ob(lim))
end

# Colimits
##########

# Colimits in Skel(FinSet)
#-------------------------

colimit(Xs::EmptyDiagram{<:FinSet{Int}}) = Colimit(Xs, SMulticospan{0}(FinSet(0)))

function universal(colim::Initial{<:FinSet{Int}}, cocone::SMulticospan{0})
  cod = apex(cocone)
  FinDomFunction(SVector{0,eltype(cod)}(), cod)
end

colimit(Xs::SingletonDiagram{<:FinSet{Int}}) = colimit(Xs, SpecializeColimit())

function colimit(Xs::ObjectPair{<:FinSet{Int}})
  m, n = length.(Xs)
  ι1 = FinFunction(1:m, m, m+n)
  ι2 = FinFunction(m+1:m+n, n, m+n)
  Colimit(Xs, Cospan(ι1, ι2))
end

function universal(colim::BinaryCoproduct{<:FinSet{Int}}, cocone::Cospan)
  f, g = cocone
  FinDomFunction(vcat(collect(f), collect(g)), ob(colim), apex(cocone))
end

function colimit(Xs::DiscreteDiagram{<:FinSet{Int}})
  ns = length.(Xs)
  n = sum(ns)
  offsets = [0,cumsum(ns)...]
  ιs = [FinFunction((1:ns[j]) .+ offsets[j],ns[j],n) for j in 1:length(ns)]
  Colimit(Xs, Multicospan(FinSet(n), ιs))
end

function universal(colim::Coproduct{<:FinSet{Int}}, cocone::Multicospan)
  cod = apex(cocone)
  FinDomFunction(mapreduce(collect, vcat, cocone, init=eltype(cod)[]),
                 ob(colim), cod)
end

function colimit(pair::ParallelPair{<:FinSet{Int}})
  f, g = pair
  m, n = length(dom(pair)), length(codom(pair))
  sets = IntDisjointSets(n)
  for i in 1:m
    union!(sets, f(i), g(i))
  end
  Colimit(pair, SMulticospan{1}(quotient_projection(sets)))
end

function colimit(para::ParallelMorphisms{<:FinSet{Int}})
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m, n = length(dom(para)), length(codom(para))
  sets = IntDisjointSets(n)
  for i in 1:m
    for f in frest
      union!(sets, f1(i), f(i))
    end
  end
  Colimit(para, SMulticospan{1}(quotient_projection(sets)))
end

function universal(coeq::Coequalizer{<:FinSet{Int}}, cocone::SMulticospan{1})
  pass_to_quotient(proj(coeq), only(cocone))
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
function pass_to_quotient(π::FinFunction{Int,Int}, h::FinFunction{Int,Int})
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

function pass_to_quotient(π::FinFunction{Int,Int}, h::FinDomFunction{Int})
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

function colimit(span::Multispan{<:FinSet{Int}})
  colimit(span, ComposeCoproductCoequalizer())
end

""" Colimit of general diagram of FinSets computed by coproduct-then-quotient.

See `Limits.CompositePushout` for a very similar construction.
"""
struct FinSetCompositeColimit{Ob<:FinSet, Diagram,
                              Cocone<:Multicospan{Ob}, Coprod<:Coproduct{Ob},
                              Proj<:FinFunction} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  coprod::Coprod
  proj::Proj # Projection for the "multi-coequalizer" in general formula.
end

function colimit(d::BipartiteFreeDiagram{<:FinSet{Int}})
  # As in a pushout, this method assume that all objects in layer 1 have
  # outgoing morphisms so that they can be excluded from the coproduct.
  @assert !any(isempty(incident(d, u, :src)) for u in vertices₁(d))
  coprod = coproduct(ob₂(d))
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
  cocone = Multicospan(codom(π), [ ιs[i]⋅π for i in vertices₂(d) ])
  FinSetCompositeColimit(d, cocone, coprod, π)
end

colimit(d::FreeDiagram{<:FinSet{Int}}) = colimit(FinDomFunctor(d))

function colimit(F::Functor{<:FinCat{Int},<:TypeCat{<:FinSet{Int}}})
  # Uses the general formula for colimits in Set (Leinster, 2014, Basic Category
  # Theory, Example 5.2.16).
  J = dom(F)
  coprod = coproduct(map(x -> ob_map(F, x), ob_generators(J)))
  n, ιs = length(ob(coprod)), legs(coprod)
  sets = IntDisjointSets(n)
  for f in hom_generators(J)
    s, t, h = dom(J, f), codom(J, f), hom_map(F, f)
    for i in dom(h)
      union!(sets, ιs[s](i), ιs[t](h(i)))
    end
  end
  π = quotient_projection(sets)
  cocone = Multicospan(codom(π), map(x -> ιs[x]⋅π, ob_generators(J)))
  FinSetCompositeColimit(F, cocone, coprod, π)
end

function universal(colim::FinSetCompositeColimit, cocone::Multicospan)
  h = universal(colim.coprod, cocone)
  pass_to_quotient(colim.proj, h)
end

# Colimits with names
#--------------------

""" Compute colimit of finite sets whose elements are meaningfully named.

This situation seems to be mathematically uninteresting but is practically
important. The colimit is computed by reduction to the skeleton of **FinSet**
(`FinSet{Int}`) and the names are assigned afterwards, following some reasonable
conventions and add tags where necessary to avoid name clashes.
"""
struct NamedColimit <: ColimitAlgorithm end

function colimit(::Type{<:Tuple{<:FinSet{<:Any,T},<:FinFunction}}, d) where
    {T <: Union{Symbol,AbstractString}}
  colimit(d, NamedColimit())
end

function colimit(d::FixedShapeFreeDiagram{<:FinSet{<:Any,T},Hom},
                 alg::NamedColimit) where {T,Hom}
  # Reducing to the case of bipartite free diagrams is a bit lazy, but at least
  # using `SpecializeColimit` below should avoid some gross inefficiencies.
  colimit(BipartiteFreeDiagram{FinSet{<:Any,T},Hom}(d), alg)
end
function colimit(d::BipartiteFreeDiagram{<:FinSet{<:Any,T}}, ::NamedColimit) where T
  # Compute colimit of diagram in the skeleton of FinSet (`FinSet{Int}`).
  # Note: no performance would be gained by using `DisjointSets{T}` from
  # DataStructures.jl because it is just a wrapper around `IntDisjointSets` that
  # internally builds the very same indices that we use below.
  sets₁_skel = map(set -> skeletize(set, index=false), ob₁(d))
  sets₂_skel = map(set -> skeletize(set, index=true), ob₂(d))
  funcs = map(edges(d)) do e
    skeletize(hom(d,e), sets₁_skel[src(d,e)], sets₂_skel[tgt(d,e)])
  end
  d_skel = BipartiteFreeDiagram{FinSetInt,eltype(funcs)}()
  add_vertices₁!(d_skel, nv₁(d), ob₁=dom.(sets₁_skel))
  add_vertices₂!(d_skel, nv₂(d), ob₂=dom.(sets₂_skel))
  add_edges!(d_skel, src(d), tgt(d), hom=funcs)
  colim_skel = colimit(d_skel, SpecializeColimit())

  # Assign elements/names to the colimit set.
  elems = Vector{T}(undef, length(apex(colim_skel)))
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
    FinFunction(Dict(Y(i) => elems[ι(i)] for i in dom(Y)), FinSet(elems))
  end
  Colimit(d, Multicospan(FinSet(elems), ιs))
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

# Subsets
#########

""" Subset of a finite set.
"""
const SubFinSet{S,T} = Subobject{<:FinSet{S,T}}

Subobject(X::FinSet, f) = Subobject(FinFunction(f, X))
SubFinSet(X, f) = Subobject(FinFunction(f, X))

force(A::SubFinSet{Int}) = Subobject(force(hom(A)))
Base.collect(A::SubFinSet) = collect(hom(A))
Base.sort(A::SubFinSet) = SubFinSet(ob(A), sort(collect(A)))

const AbstractBoolVector = Union{AbstractVector{Bool},BitVector}

""" Subset of a finite set represented as a boolean vector.

This is the subobject classifier representation since `Bool` is the subobject
classifier for `Set`.
"""
@struct_hash_equal struct SubFinSetVector{S<:FinSet} <: Subobject{S}
  set::S
  predicate::AbstractBoolVector

  function SubFinSetVector(X::S, pred::AbstractBoolVector) where S<:FinSet
    length(pred) == length(X) ||
      error("Size of predicate $pred does not equal size of object $X")
    new{S}(X, pred)
  end
end

Subobject(X::FinSet, pred::AbstractBoolVector) = SubFinSetVector(X, pred)
SubFinSet(pred::AbstractBoolVector) = Subobject(FinSet(length(pred)), pred)

ob(A::SubFinSetVector) = A.set
hom(A::SubFinSetVector) = FinFunction(findall(A.predicate), A.set)
predicate(A::SubFinSetVector) = A.predicate

function predicate(A::SubFinSet)
  f = hom(A)
  pred = falses(length(codom(f)))
  for x in dom(f)
    pred[f(x)] = true
  end
  pred
end

@instance ThSubobjectLattice{FinSet,SubFinSet} begin
  @import ob
  meet(A::SubFinSet, B::SubFinSet) = meet(A, B, SubOpBoolean())
  join(A::SubFinSet, B::SubFinSet) = join(A, B, SubOpBoolean())
  top(X::FinSet) = top(X, SubOpWithLimits())
  bottom(X::FinSet) = bottom(X, SubOpWithLimits())
end

""" Algorithm to compute subobject operations using elementwise boolean logic.
"""
struct SubOpBoolean <: SubOpAlgorithm end

meet(A::SubFinSet{Int}, B::SubFinSet{Int}, ::SubOpBoolean) =
  SubFinSet(predicate(A) .& predicate(B))
join(A::SubFinSet{Int}, B::SubFinSet{Int}, ::SubOpBoolean) =
  SubFinSet(predicate(A) .| predicate(B))
top(X::FinSet{Int}, ::SubOpBoolean) = SubFinSet(trues(length(X)))
bottom(X::FinSet{Int}, ::SubOpBoolean) = SubFinSet(falses(length(X)))

end
