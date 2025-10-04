
module FinSetCatLimits

using DataStructures, StructEquality, StaticArrays

using GATlab, ACSets

using .....Theories, .....Graphs, .....BasicSets
using ....Cats
using ..FinSetCat: FinSetC
using ...SkelFinSetCat: FinSetIndexedLimit


############
# Terminal #
############

@instance ThCategoryWithTerminal{FinSet, FinFunction} [model::FinSetC] begin 
  limit(::EmptyDiagram)::AbsLimit = 
    TerminalLimit{FinSet,FinFunction}(FinSet(nothing))

  universal(::AbsLimit, ::EmptyDiagram, a::Multispan) = 
    FinFunction(ConstantFunction(nothing, apex(a), FinSet(nothing)))

end

############
# Products #
############

@instance ThCategoryUnbiasedProducts{FinSet, FinFunction} [model::FinSetC] begin 

  function limit(d::DiscreteDiagram)::AbsLimit  
    Xs = collect(d)
    P = ProdSet(Xs) |> FinSet
    πs = [FinFunction(tup -> tup[j], P, X) for (j, X) in enumerate(Xs)]
    LimitCone(Multispan(P, πs, Xs), FreeDiagram(d))
  end

  universal(lim::AbsLimit, ::DiscreteDiagram, fs::Multispan) = 
    FinFunction(i -> tuple([f(i) for f in fs]...), apex(fs), ob(lim))

end


##############
# Equalizers #
##############

@instance ThCategoryWithEqualizers{FinSet, FinFunction} [model::FinSetC] begin 

  function limit(para::ParallelMorphisms)::AbsLimit  
    @assert !isempty(para)
    d = dom(para)
    eq_test(i) = allequal([f(i) for f in para])
    eq = FinFunction(Dict(x=>x for x in collect(d) if eq_test(x)), d)
    LimitCone(Multispan(dom[model](eq), [eq]; cat=model), FreeDiagram(para))
  end

  function universal(res::AbsLimit, ::ParallelMorphisms, x::Multispan) 
    ι = collect(only(cone(res)))
    h = only(x)
    FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], length(ι))
  end  
end

@instance ThCategoryWithPullbacks{FinSet, FinFunction} [model::FinSetC] begin 
  function limit(cospan::Multicospan)::AbsLimit  
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
      return FinSetIndexedLimit(Multispan(x, πs), FreeDiagram(cospan))
    end
    # In the general case, for now we always just do a hash join, although
    # sort-merge joins can sometimes be faster.
    hash_join(cospan, model)
  end

  function universal(res::AbsLimit, ::Multicospan, x::Multispan) 
    error("TODO")
  end  
end

@instance ThCategoryWithBipartiteLimits{FinSet, FinFunction} [model::FinSetC] begin 
  function limit(d::BipartiteFreeDiagram)::AbsLimit  
    # As in a pullback, this method assumes that all objects in layer 2 have
    # incoming morphisms.
    @assert !any(isempty(incident(d, v, :tgt)) for v in vertices₂(d))
    d_original = d

    # It is generally optimal to compute all equalizers (self joins) first, so as
    # to reduce the sizes of later pullbacks (joins) and products (cross joins).
    d, ιs = equalize_all(model, d)
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
        FinSetIndexedLimit(FreeDiagram(d_original), SMultispan{1}(ιs[1]))
      else
        πs = legs(product(SVector(ob₁(d)...)))
        FinSetIndexedLimit(d_original, Multispan(map(compose, πs, ιs); cat=SkelFinSet()))
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
      pb = pullback[model](SVector(hom(d, join_edges)...))

      # Create a new bipartite diagram with joined vertices.
      d_joined = BipartiteFreeDiagram{FinSet,FinFunction}()
      copy_parts!(d_joined, d, V₁=to_keep, V₂=setdiff(vertices₂(d),v), E=edges(d))
      joined = add_vertex₁!(d_joined, ob₁=apex(pb))
      for (u, π) in zip(to_join, legs(pb))
        for e in setdiff(incident(d, u, :src), join_edges)
          set_subparts!(d_joined, e, src=joined, hom=π⋅hom(d,e))
        end
      end
      rem_edges!(d_joined, join_edges)

      # Recursively compute the limit of the new diagram.
      lim = limit[model](d_joined)

      # Assemble limit cone from cones for pullback and reduced limit.
      πs = Vector{FinFunction}(undef, nv₁(d))
      for (i, u) in enumerate(to_join)
        πs[u] = compose[model](last(legs(lim)), compose[model](legs(pb)[i], ιs[u]))
      end
      for (i, u) in enumerate(to_keep)
        πs[u] = compose(legs(lim)[i], ιs[u])
      end
      FinSetIndexedLimit(FreeDiagram(d_original), Multispan(πs; cat=model))
    end
  end

  function universal(res::AbsLimit, ::BipartiteFreeDiagram, x::Multispan) 
    error("TODO")
  end 
end

##################
# Tabular limits #
##################

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
@struct_hash_equal struct TabularLimit <: AbsLimit
  cone::Multispan
end

function TabularLimit(lim::AbsLimit; names=nothing)
  πs = legs(lim)
  names = isnothing(names) ? (1:length(πs)) : names
  names = Tuple(column_name(name) for name in names)
  table = TabularSet(NamedTuple{names}(Tuple(map(collect, πs))))
  cone = Multispan(table, map(πs, eachindex(πs)) do π, i
    FinFunction(row -> Tables.getcolumn(row, i), table, codom(π))
  end)
  Limit(lim.diagram, cone)
end

function universal(::Diagram, lim::TabularLimit,cone::Multispan)
  fs = Tuple(legs(cone))
  FinFunction(x -> Row(map(f -> f(x), fs)), apex(cone), ob(lim))
end

column_name(name) = Symbol(name)
column_name(i::Integer) = Symbol("x$i") # Same default as DataFrames.jl.


#############
# Hash Join #
#############

function hash_join(cospan::Multicospan{Ob, Hom}, model) where {Ob,Hom}
  # We follow the standard terminology for hash joins: in a multiway hash join,
  # one function, called the *probe*, will be iterated over and need not be
  # indexed, whereas the other functions, call *build* inputs, must be indexed.
  #
  # We choose as probe the unindexed function with largest domain. If all
  # functions are already indexed, we arbitrarily choose the first one.
  i = argmax(map(legs(cospan)) do f
    is_indexed(f) ? -1 : length(dom[model](f))
  end)
  probe = legs(cospan)[i]
  builds = map(ensure_indexed, deleteat(legs(cospan), i))
  πs_build, π_probe = hash_join(builds, probe)
  FinSetIndexedLimit(cospan, Multispan(insert(πs_build, i, π_probe)))
end

deleteat(vec::Vector, i) = deleteat!(copy(vec), i)
deleteat(vec::StaticVector, i) = StaticArrays.deleteat(vec, i)

insert(vec::Vector{T}, i, x::S) where {T,S} = 
  insert!(collect(typejoin(T,S), vec), i, x)

insert(vec::StaticVector{N,T}, i, x::S) where {N,T,S} =
  StaticArrays.insert(similar_type(vec, typejoin(T,S))(vec), i, x)

""" Coerce probe to a FinDomFunction """
hash_join(builds::AbstractVector, probe::FinFunction) = 
  hash_join(builds, FinDomFunction(probe))

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

function hash_join(build::FinDomFunction, probe::FinDomFunction)
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


#################
# SortMergeJoin #
#################

function sort_merge_limit(cospan::Multicospan{Ob,Hom}) where {Ob,Hom}
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
  FinSetIndexedLimit(cone, FreeDiagram(cospan))
end

similar_mutable(x::AbstractVector, T::Type) = similar(x, T)


##################
# NestedLoopJoin #
##################

"""
A nested-loop join is algorithmically the same as `ComposeProductEqualizer`,
but for completeness and performance we give a direct implementation here.
"""
function nested_loop_limit(cospan::Multicospan{Ob,Hom}) where {Ob,Hom}
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
  Limit(Diagram(cospan, Category(TypeCat(m))), FinSetIndexedLimit(cone))
end



""" Compute all possible equalizers in a bipartite free diagram.

The result is a new bipartite free diagram that has the same vertices but is
*simple*, i.e., has no multiple edges. The list of inclusion morphisms into
layer 1 of the original diagram is also returned.
"""
function equalize_all(model, d::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom}
  d_simple = BipartiteFreeDiagram{Ob,Hom}()
  copy_parts!(d_simple, d, V₂=vertices₂(d))
  ιs = map(vertices₁(d)) do u
    # Collect outgoing edges of u, key-ed by target vertex.
    out_edges = OrderedDict{Int,Vector{Int}}()
    for e in incident(d, u, :src)
      push!(get!(out_edges, tgt(d,e)) do; Int[] end, e)
    end

    # Equalize all sets of parallel edges out of u.
    ι = id[model](ob₁(d, u))
    for es in values(out_edges)
      if length(es) > 1
        fs = SVector([compose[model](ι,f) for f in hom(d, es)])
        ι = compose[model](incl(equalizer(fs), ι))
      end
    end

    add_vertex₁!(d_simple, ob₁=dom(ι)) # == u
    for (v, es) in pairs(out_edges)
      add_edge!(d_simple, u, v, hom=compose[model](ι,hom(d, first(es))))
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
      prod = product(ob₂(d, tgts))
      v = add_vertex₂!(d_paired, ob₂=ob(prod))
      for (i,u) in enumerate(srcs)
        f = pair(prod, hom(d, getindex.(in_edges, i)))
        add_edge!(d_paired, u, v, hom=f)
      end
    end
  end
  d_paired
end

end #module
