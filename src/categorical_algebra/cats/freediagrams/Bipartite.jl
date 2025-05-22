module Bipartite

export BipartiteFreeDiagram, ob₁, ob₂, nv₁, nv₂, 
      vertices₁, vertices₂, add_vertex₁!, add_vertex₂!, add_vertices₁!,
      add_vertices₂!, specialize

using StructEquality

using ACSets, GATlab 

import .....Theories: hom, ThCategory
using .....BasicSets: FinSet
using .....Graphs
import .....Graphs: nv₁, nv₂

using ...Categories: obtype, homtype
using ..FreeDiagrams
import ..FreeDiagrams: fmap, cone_objects, cocone_objects, specialize

using .ThFreeDiagram


@abstract_acset_type _BipartiteFreeDiagram <: AbstractUndirectedBipartiteGraph

""" A free diagram with a bipartite structure.

Such diagrams include most of the fixed shapes, such as spans, cospans, and
parallel morphisms. They are also the generic shape of diagrams for limits and
colimits arising from undirected wiring diagrams. For limits, the boxes
correspond to vertices in ``V₁`` and the junctions to vertices in ``V₂``.
Colimits are dual.
"""
const BipartiteFreeDiagram{Ob,Hom,S} = _BipartiteFreeDiagram{S,Tuple{Ob,Hom}}

@present SchBipartiteFreeDiagram <: SchUndirectedBipartiteGraph begin
  Ob::AttrType
  Hom::AttrType
  ob₁::Attr(V₁, Ob)
  ob₂::Attr(V₂, Ob)
  hom::Attr(E, Hom)
end

""" The default concrete type for bipartite free diagrams.
"""
@acset_type BasicBipartiteFreeDiagram(SchBipartiteFreeDiagram,
  index=[:src, :tgt]) <: _BipartiteFreeDiagram

@present SchFreeDiagramAsBipartite <: SchBipartiteFreeDiagram begin
  V::Ob
  orig_vert₁::Hom(V₁, V)
  orig_vert₂::Hom(V₂, V)
end

""" A free diagram that has been converted to a bipartite free diagram.
"""
@acset_type FreeDiagramAsBipartite(SchFreeDiagramAsBipartite,
  index=[:src, :tgt], unique_index=[:orig_vert₁, :orig_vert₂]) <: _BipartiteFreeDiagram

ob₁(d::BipartiteFreeDiagram, args...) = subpart(d, args..., :ob₁)
ob₂(d::BipartiteFreeDiagram, args...) = subpart(d, args..., :ob₂)
hom(d::BipartiteFreeDiagram, args...) = subpart(d, args..., :hom)

diagram_type(::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom} = Tuple{Ob,Hom}
cone_objects(diagram::BipartiteFreeDiagram) = ob₁(diagram)
cocone_objects(diagram::BipartiteFreeDiagram) = ob₂(diagram)

BipartiteFreeDiagram{Ob,Hom}() where {Ob,Hom} =
  BasicBipartiteFreeDiagram{Ob,Hom}()

BipartiteFreeDiagram(obs₁::AbstractVector{Ob₁}, obs₂::AbstractVector{Ob₂},
                     homs::AbstractVector{Tuple{Hom,Int,Int}}; cat=nothing) where {Ob₁,Ob₂,Hom} =
  BipartiteFreeDiagram{Union{Ob₁,Ob₂},Hom}(obs₁, obs₂, homs; cat)

function BipartiteFreeDiagram{Ob,Hom}(obs₁::AbstractVector, obs₂::AbstractVector,
                                      homs::AbstractVector; cat=nothing) where {Ob,Hom}

  cat = isnothing(cat) ? Dispatch(ThCategory, [Ob,Hom]) : cat
  for (f,s,t) in homs
    obs₁[s] == dom[cat](f) || error("Bad dom($f) = $(dom[cat](f)) ≠ $(obs₁[s])")
    obs₂[t] == codom[cat](f) || error("Bad codom($f) = $(codom[cat](f)) ≠ $(obs₂[t])")
  end

  d = BipartiteFreeDiagram{Ob,Hom}()
  add_vertices₁!(d, length(obs₁), ob₁=obs₁)
  add_vertices₂!(d, length(obs₂), ob₂=obs₂)
  add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

function BipartiteFreeDiagram(discrete::DiscreteDiagram{Ob};
                                      colimit::Bool=false) where {Ob}
  # error if use Union{} ... this is incorrect while we wait for the bug to be 
  # fixed in Julia 1.12 
  d = BipartiteFreeDiagram{Ob,Nothing}() 
  if colimit
    add_vertices₂!(d, length(discrete), ob₂=collect(discrete))
  else
    add_vertices₁!(d, length(discrete), ob₁=collect(discrete))
  end
  return d
end

BipartiteFreeDiagram(span::Multispan{O,H}) where {O,H} = 
  BipartiteFreeDiagram{O,H}(span)

function BipartiteFreeDiagram{Ob,Hom}(span::Multispan{O,H}) where {Ob,Hom, O<:Ob, H<:Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₁!(d, ob₁=apex(span))
  vs = add_vertices₂!(d, length(span), ob₂=feet(span))
  add_edges!(d, fill(v₀, length(span)), vs, hom=legs(span))
  return d
end

BipartiteFreeDiagram(span::Multicospan{O,H}) where {O,H} = 
  BipartiteFreeDiagram{O,H}(span)

function BipartiteFreeDiagram{Ob,Hom}(cospan::Multicospan) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₂!(d, ob₂=apex(cospan))
  vs = add_vertices₁!(d, length(cospan), ob₁=feet(cospan))
  add_edges!(d, vs, fill(v₀, length(cospan)), hom=legs(cospan))
  return d
end

function BipartiteFreeDiagram(para::ParallelMorphisms{Ob,Hom}; 
                              cat=nothing) where {Ob,Hom} 
  O,H = isnothing(cat) ? (Ob,Hom) : impl_type.(Ref(cat),Ref(ThCategory), [:Ob,:Hom])
  BipartiteFreeDiagram{O,H}(para)
end

function BipartiteFreeDiagram{Ob,Hom}(para::ParallelMorphisms) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₁ = add_vertex₁!(d, ob₁=dom(para))
  v₂ = add_vertex₂!(d, ob₂=codom(para))
  add_edges!(d, fill(v₁,length(para)), fill(v₂,length(para)), hom=collect(para))
  return d
end

cocone_indices(d::FreeDiagramAsBipartite) = d[:orig_vert₂]

cocone_indices(d::BasicBipartiteFreeDiagram) = parts(d,:V₂)

@instance ThFreeDiagram{Int,Int,Ob,Hom
                       } [model::_BipartiteFreeDiagram{S,Tuple{Ob,Hom}}
                         ] where {S, Ob, Hom} begin
  src(e::Int)::Int = src(model, e)
  tgt(e::Int)::Int = tgt(model, e) + nv₁(model) 
  function obmap(x::Int)::Ob 
    if x ≤ nv₁(model) 
      ob₁(model, x)
    else 
      ob₂(model, x - nv₁(model))
    end
  end
  hommap(x::Int)::Hom = hom(model, x)
  obset()::FinSet = FinSet(sum(nv(model)))
  homset()::FinSet = FinSet(ne(model))
end

# """ Convert a free diagram to a bipartite free diagram.

# Reduce a free diagram to a free bipartite diagram with the same limit (the
# default, `colimit=false`) or the same colimit (`colimit=true`). The reduction is
# essentially the same in both cases, except for the choice of where to put
# isolated vertices, where we follow the conventions described at
# [`cone_objects`](@ref) and [`cocone_objects`](@ref). The resulting object is a
# bipartite free diagram equipped with maps from the vertices of the bipartite
# diagram to the vertices of the original diagram.
# """
function BipartiteFreeDiagram{Ob,Hom}(F::FreeDiagram;
                                      colimit::Bool=false) where {Ob,Hom}
  d = FreeDiagramAsBipartite{Ob,Hom}()
  g = FreeGraph(F)
  add_parts!(d, :V, nv(g))
  for (v, o) in zip(vertices(g), obset(F))
    x = obmap(F, o)
    out_edges, in_edges = incident(g, v, :src), incident(g, v, :tgt)
    v₁ = if !isempty(out_edges) || (!colimit && isempty(in_edges))
      add_vertex₁!(d, ob₁=x, orig_vert₁=v)
    end
    v₂ = if !isempty(in_edges) || (colimit && isempty(out_edges))
      add_vertex₂!(d, ob₂=x, orig_vert₂=v)
    end
    if !(isnothing(v₁) || isnothing(v₂))
      add_edge!(d, v₁, v₂, hom=id(x))
    end
  end
  for e in edges(g)
    v₁ = only(incident(d, src(g, e), :orig_vert₁))
    v₂ = only(incident(d, tgt(g, e), :orig_vert₂))
    add_edge!(d, v₁, v₂, hom=hommap(F, e))
  end
  return d
end

BipartiteFreeDiagram(F::FreeDiagram) = 
  BipartiteFreeDiagram{obtype(F), homtype(F)}(F)


function specialize(::Type{BipartiteFreeDiagram}, d::FreeDiagram)
  BipartiteFreeDiagram{impl_type(d, :Ob), impl_type(d, :Hom)}(d)
end

""" Replace homs via a replacement function """
function fmap(d::BasicBipartiteFreeDiagram, o, h, O::Type, H::Type) 
  res = BasicBipartiteFreeDiagram{O,H}()
  add_vertices₁!(res, nparts(d, :V₁), ob₁=o.(d[:ob₁]))
  add_vertices₂!(res, nparts(d, :V₂), ob₂=o.(d[:ob₂]))
  for e in edges(d)
    add_edge!(res, src(d, e), tgt(d, e); hom=h(hom(d,e)))
  end
  res
end

end # module
