module Limits 
using DataStructures, StructEquality, StaticArrays

using GATlab, ACSets

using .....Theories, .....Graphs, .....BasicSets
using ....Cats
using ...SetCats: FinSetIndexedLimit, FinSetC
using ..SetCat: SetC

############
# Products #
############

@instance ThCategoryUnbiasedProducts{SetOb,SetFunction} [model::SetC] begin 

  function limit(a::DiscreteDiagram)::AbsLimit
    feet = SetOb[a...]
    X = SetOb(ProdSet(feet))
    πs = [ SetFunction(x -> getindex(x, i), X, Xi) for (i, Xi) in enumerate(a)]
    LimitCone(Multispan{SetOb,SetFunction, SetOb}(X, πs, feet), FreeDiagram(a))
  end  

  function universal(res::AbsLimit, ::DiscreteDiagram, span::Multispan) 
    @assert length(cone(res)) == length(span)
    fs = Tuple(legs(span))
    SetFunction(x -> map(f -> f(x), fs), apex(span), ob(res))
  end
end

##############
# Equalizers #
##############

@instance ThCategoryWithEqualizers{SetOb, SetFunction} [model::SetC] begin 

  function limit(para::ParallelMorphisms)::AbsLimit  
    @assert !isempty(para)
    f1, frest = coerce_findom(para[1]), coerce_findom.(para[2:end])
    domset = collect(FinSet(dom(para)))
    eq = SetFunction(identity, SetOb(FinSet(Set(filter(i -> all(f->f1(i) == f(i), frest), domset)))), dom(para))
    LimitCone(Multispan(dom[model](eq), [eq]; cat=model), FreeDiagram(para))
  end

  function universal(res::AbsLimit, ::ParallelMorphisms, x::Multispan) 
    ι = collect(only(cone(res)))
    h = only(x)
    SetFunction(FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], length(ι)))
  end  
end


#############
# Pullbacks #
#############
# THIS CODE SEEMS TO RELY ON SOME OF THE FUNCTIONS BEING FINDOMFUNCTIONS
@instance ThCategoryWithPullbacks{SetOb, SetFunction} [model::SetC] begin 
  function limit(cospan::Multicospan)::AbsLimit 
    # Handle the important special case where one of the legs is a constant
    # (function out of a singleton set). In this case, we just need to take a
    # product of preimages of the constant value.
    funcs = legs(cospan)
    i = findfirst(f -> length(dom(f)) == 1, funcs)
    if !isnothing(i)
      c = funcs[i](1)
      ιs = map(deleteat′(funcs, i)) do f
        SetFunction(FinFunction(preimage(coerce_findom(f), c), FinSet(dom(f))))
      end
      x, πs = if length(ιs) == 1
        dom(only(ιs)), ιs
      else
        prod = limit[model](DiscreteDiagram(map(dom, ιs)))
        ob[model](prod), map(compose[model], legs(prod), ιs)
      end
      πs = insert′(πs, i, SetFunction(ConstantFunction(1, x, SetOb(1))))
      return FinSetIndexedLimit(FreeDiagram(cospan), Multispan(x, πs))
    end
    # In the general case, for now we always just do a hash join, although
    # sort-merge joins can sometimes be faster.
    hash_join(cospan, model)
  end

  function universal(res::AbsLimit, ::Multicospan, x::Multispan) 
    error("TODO")
  end  
end


function hash_join(cospan::Multicospan{Ob, Hom}, model) where {Ob,Hom}
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
  builds = map(ensure_indexed, deleteat′(legs(cospan), i))
  πs_build, π_probe = hash_join(builds, probe)
  FinSetIndexedLimit(cospan, Multispan(insert′(πs_build, i, π_probe)))
end

# DO WE NEED THIS?
deleteat′(vec::Vector, i::Int) = deleteat!(copy(vec), i)
deleteat′(vec::StaticVector, i::Int) = StaticArrays.deleteat(vec, i)

insert′(vec::Vector{T}, i, x::S) where {T,S} = 
  insert!(collect(typejoin(T,S), vec), i, x)

insert′(vec::StaticVector{N,T}, i, x::S) where {N,T,S} =
  StaticArrays.insert(similar_type(vec, typejoin(T,S))(vec), i, x)

function hash_join(builds::AbstractVector, probe::SetFunction)
  π_builds, πp = map(_ -> Int[], builds), Int[]
  for y in dom(probe)
    val = probe(y)
    preimages = map(build -> preimage(coerce_findom(build), val), builds)
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
  to_probe = SetFunction(FinFunction(πp, FinSet(dom(probe))))
  (SetFunction.(FinFunction.(π_builds, FinSet.(dom.(builds)))), to_probe)
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

#############
# Bipartite #
#############

@instance ThCategoryWithBipartiteLimits{SetOb, SetFunction} [model::SetC] begin 
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
    d = pair_all(model, d)

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
        πs = legs(limit[model](DiscreteDiagram(SVector(ob₁(d)...))))
        FinSetIndexedLimit(FreeDiagram(d_original), 
                           Multispan(map(compose[model], πs, ιs); cat=model))
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
      d_joined = BipartiteFreeDiagram{SetOb,SetFunction}()
      copy_parts!(d_joined, d, V₁=to_keep, V₂=setdiff(vertices₂(d),v), E=edges(d))
      joined = add_vertex₁!(d_joined, ob₁=apex(pb))
      for (u, π) in zip(to_join, legs(pb))
        for e in setdiff(incident(d, u, :src), join_edges)
          set_subparts!(d_joined, e, src=joined, hom=compose[model](π,hom(d,e)))
        end
      end
      rem_edges!(d_joined, join_edges)

      # Recursively compute the limit of the new diagram.
      lim = limit[model](d_joined)

      # Assemble limit cone from cones for pullback and reduced limit.
      πs = Vector{SetFunction}(undef, nv₁(d))
      for (i, u) in enumerate(to_join)
        πs[u] = compose[model](last(legs(lim)), compose[model](legs(pb)[i], ιs[u]))
      end
      for (i, u) in enumerate(to_keep)
        πs[u] = compose[model](legs(lim)[i], ιs[u])
      end
      FinSetIndexedLimit(FreeDiagram(d_original), Multispan(πs; cat=model))
    end
  end

  function universal(res::AbsLimit, ::BipartiteFreeDiagram, x::Multispan) 
    error("TODO $res")
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
        fs = ParallelMorphisms(map(hom(d, es)) do f 
          compose[model](ι,f)
        end)
        ι = compose[model](incl(limit[model](fs)), ι)
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
function pair_all(model, d::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom}
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
      prod = limit[model](DiscreteDiagram(ob₂(d, tgts)))
      v = add_vertex₂!(d_paired, ob₂=ob(prod))
      for (i,u) in enumerate(srcs)
        f = pair[model](prod, hom(d, getindex.(in_edges, i)))
        add_edge!(d_paired, u, v, hom=f)
      end
    end
  end
  d_paired
end

end # module
