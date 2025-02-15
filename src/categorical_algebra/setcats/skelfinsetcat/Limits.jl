module Limits 

export FinSetIndexedLimit

using StaticArrays, DataStructures

using ACSets, GATlab

using .....Theories, .....Graphs, .....BasicSets,  ....Cats
import ....Cats: composite_universal

using ..SkelFinSetCat

############
# Terminal #
############

@instance ThCategoryWithTerminal{FinSetInt, FinFunction} [model::SkelFinSet] begin 
  limit(::EmptyDiagram)::AbsLimit = 
    TerminalLimit{FinSetInt,FinFunction}(FinSetInt(1))

  universal(::AbsLimit, ::EmptyDiagram, a::Multispan) = 
    FinFunction(ConstantFunction(1, FinSet(apex[model](a)), FinSet(1)))
end

############
# Products #
############

@instance ThCategoryUnbiasedProducts{FinSetInt, FinFunction} [model::SkelFinSet] begin

  function limit(Xs::DiscreteDiagram)::AbsLimit
    ns = length.(Xs)
    indices = CartesianIndices(Tuple(ns))
    n = prod(Vector{Int}(ns))
    πs = [FinFunction(i -> indices[i][j], FinSet(n), FinSet(ns[j])) 
          for j in 1:length(ns)]
    LimitCone(Multispan(FinSetInt(n), πs, FinSetInt.(ns)), 
              FreeDiagram(Xs))
  end

  function universal(p::AbsLimit, ::DiscreteDiagram, span::Multispan)
    ns = length.(codom.(span))
    indices = LinearIndices(Tuple(ns))
    v = map(apex(span)) do i 
      indices[(f(i) for f in span)...]
    end
    FinFunction(v, FinSet(apex(p)))
  end
end

##############
# Equalizers #
##############

@instance ThCategoryWithEqualizers{FinSetInt, FinFunction} [model::SkelFinSet] begin

  function limit(para::ParallelMorphisms)
    @assert !isempty(para)
    f1, frest = para[1], para[2:end]
    m = length(dom(para))
    eq = FinFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m), m)
    LimitCone(Multispan(dom[model](eq), [eq]; cat=model), FreeDiagram(para))
  end 
  
  function universal(res::AbsLimit, ::ParallelMorphisms, span::Multispan)
    ι = collect(only(cone(res)))
    h = only(span)
    FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom[model](h)], 
                length(ι))
  end 

end

#############
# Pullbacks #
#############

""" Limit of finite sets with a reverse mapping or index into the limit set.

This type provides a fallback for limit algorithms that do not come with a
specialized algorithm to apply the universal property of the limit. In such
cases, you can explicitly construct a mapping from tuples of elements in the
feet of the limit cone to elements in the apex of the cone.

The index is constructed the first time it is needed. Thus there is no extra
cost to using this type if the universal property will not be invoked.
"""
mutable struct FinSetIndexedLimit <: AbsLimit
  diagram::FreeDiagram
  cone::Multispan
  index::Union{AbstractDict,Nothing}
  FinSetIndexedLimit(d::FreeDiagram, c::Multispan) = new(d, c, nothing)
end

diagram(f::FinSetIndexedLimit) = f.diagram

FinSetIndexedLimit(diagram::Multicospan, cone::Multispan) =
  FinSetIndexedLimit(FreeDiagram(diagram), cone)

function make_limit_index(cone::Multispan)
  πs = Tuple(legs(cone))
  index = Dict{Tuple{map(eltype∘codom, πs)...}, eltype(apex(cone))}()
  for x in apex(cone)
    index[map(π -> π(x), πs)] = x
  end
  return index
end

@instance ThCategoryWithPullbacks{FinSetInt, FinFunction} [model::SkelFinSet] begin

    """ 'Smart join' algorithm """
    function limit(cospan::Multicospan)
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
        πs = insert(πs, i, FinFunction(ConstantFunction(1, x, FinSet(1))))
        return FinSetIndexedLimit(cospan, Multispan(πs; cat=model))
      end
        # In the general case, for now we always just do a hash join, although
        # sort-merge joins can sometimes be faster.
      pullback_hashjoin(cospan)
    end

    universal(lim::AbsLimit, ::Multicospan, spn::Multispan) = 
      indexed_universal(lim, spn)
end

function indexed_universal(lim::FinSetIndexedLimit, spn::Multispan)
  if isnothing(lim.index)
    lim.index = make_limit_index(lim.cone)
  end
  fs = Tuple(legs(spn))
  FinFunction(Int[lim.index[map(f -> f(x), fs)] for x in apex(spn)],
              FinSet(ob(lim)))
end

deleteat(vec::StaticVector, i) = StaticArrays.deleteat(vec, i)
deleteat(vec::Vector, i) = deleteat!(copy(vec), i)

insert(vec::StaticVector{N,T}, i, x::S) where {N,T,S} =
  StaticArrays.insert(similar_type(vec, typejoin(T,S))(vec), i, x)
insert(vec::Vector{T}, i, x::S) where {T,S} =
  insert!(collect(typejoin(T,S), vec), i, x)


function pullback_hashjoin(cospan::Multicospan)

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
  FinSetIndexedLimit(cospan, Multispan(insert(πs_build, i, π_probe); cat=SkelFinSet()))
end

function hash_join(builds::AbstractVector{<:FinFunction},
                   probe::FinFunction)
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

function hash_join(builds::StaticVector{1,<:FinFunction},
                   probe::FinFunction)
  πb, πp = hash_join(builds[1], probe)
  (SVector((πb,)), πp)
end

function hash_join(build::FinFunction, probe::FinFunction)
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

#############
# Bipartite #
#############

@instance ThCategoryWithBipartiteLimits{FinSetInt, FinFunction} [model::SkelFinSet] begin

  """ 'Smart join' algorithm """
  function limit(d::BipartiteFreeDiagram)
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
      d_joined = BipartiteFreeDiagram{FinSetInt,FinFunction}()
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
      FinSetIndexedLimit(FreeDiagram(d_original), Multispan(πs; cat=SkelFinSet()))
    end
  end

  function universal(lim::AbsLimit, ::BipartiteFreeDiagram, cone::Multispan)
    indexed_universal(lim, cone)
  end
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
        fs = SVector((compose[model](ι,f) for f in hom(d, es))...)
        ι = compose[model](incl(equalizer(fs)), ι)
      end
    end

    add_vertex₁!(d_simple, ob₁=getvalue(dom(ι))) # == u
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


##############
# Free graph #
##############


""" Limit of general diagram of FinSets computed by product-then-filter.

See `Limits.CompositePullback` for a very similar construction.
"""
struct FinSetCompositeLimit <: AbsLimit
  diagram::FreeDiagram
  cone::Multispan
  prod::AbsLimit
  incl::Any # Inclusion for the "multi-equalizer" in general formula.
end

function composite_universal(lim::FinSetCompositeLimit, cone::Multispan)
  ι = collect(lim.incl)
  h = universal[SkelFinSet()](lim.prod, cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], FinSet(ob(lim)))
end


@instance ThCategoryWithLimits{FinSetInt, FinFunction} [model::SkelFinSet] begin

    function limit(d::FreeGraph)
      # Uses the general formula for limits in Set (Leinster, 2014, Basic 
      # Category Theory, Example 5.1.22 / Equation 5.16). This method is simple 
      # and direct, but extremely inefficient!
      prod = product[model](d[:ob]...)
      n, πs = length(ob(prod)), legs(prod)
      ι = FinFunction(filter(1:n) do i
        all(edges(d)) do f
          s, t, h = src(d, f), tgt(d, f), d[f, :hom]
          h(πs[s](i)) == πs[t](i)
        end
      end, n)
      
      cone = Multispan(dom[model](ι), 
                       map(x -> compose[model](ι,πs[x]), vertices(d)); 
                       cat=model)

      FinSetCompositeLimit(FreeDiagram(d), cone, prod, ι)
    end

    function universal(lim::AbsLimit, ::FreeGraph, sp::Multispan)
      composite_universal(lim, sp)
    end

end

end # module
