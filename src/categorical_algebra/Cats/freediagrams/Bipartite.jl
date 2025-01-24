module Bipartite 
export BipartiteFreeDiagram, SchBipartiteFreeDiagram, ob₁, ob₂

using ACSets, GATlab
using .....Graphs

using ...FinCats, ...Functors, ..FreeDiagrams
import ..FreeDiagrams: ob, hom, cone_objects, cocone_objects, diagram_type

# Bipartite free diagrams
#------------------------

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
                     homs::AbstractVector{Tuple{Hom,Int,Int}}) where {Ob₁,Ob₂,Hom} =
  BipartiteFreeDiagram{Union{Ob₁,Ob₂},Hom}(obs₁, obs₂, homs)

function BipartiteFreeDiagram{Ob,Hom}(obs₁::AbstractVector, obs₂::AbstractVector,
                                      homs::AbstractVector) where {Ob,Hom}
  @assert all(obs₁[s] == dom(f) && obs₂[t] == codom(f) for (f,s,t) in homs)
  d = BipartiteFreeDiagram{Ob,Hom}()
  add_vertices₁!(d, length(obs₁), ob₁=obs₁)
  add_vertices₂!(d, length(obs₂), ob₂=obs₂)
  add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

BipartiteFreeDiagram(d::FixedShapeFreeDiagram{Ob,Hom}; kw...) where {Ob,Hom} =
  BipartiteFreeDiagram{Ob,Hom}(d; kw...)

function BipartiteFreeDiagram{Ob,Hom}(discrete::DiscreteDiagram;
                                      colimit::Bool=false) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  if colimit
    add_vertices₂!(d, length(discrete), ob₂=collect(discrete))
  else
    add_vertices₁!(d, length(discrete), ob₁=collect(discrete))
  end
  return d
end

function BipartiteFreeDiagram{Ob,Hom}(span::Multispan) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₁!(d, ob₁=apex(span))
  vs = add_vertices₂!(d, length(span), ob₂=feet(span))
  add_edges!(d, fill(v₀, length(span)), vs, hom=legs(span))
  return d
end

function BipartiteFreeDiagram{Ob,Hom}(cospan::Multicospan) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₀ = add_vertex₂!(d, ob₂=apex(cospan))
  vs = add_vertices₁!(d, length(cospan), ob₁=feet(cospan))
  add_edges!(d, vs, fill(v₀, length(cospan)), hom=legs(cospan))
  return d
end

function BipartiteFreeDiagram{Ob,Hom}(para::ParallelMorphisms) where {Ob,Hom}
  d = BipartiteFreeDiagram{Ob,Hom}()
  v₁ = add_vertex₁!(d, ob₁=dom(para))
  v₂ = add_vertex₂!(d, ob₂=codom(para))
  add_edges!(d, fill(v₁,length(para)), fill(v₂,length(para)), hom=hom(para))
  return d
end

cocone_indices(d::FreeDiagramAsBipartite) = d[:orig_vert₂]
cocone_indices(d::BasicBipartiteFreeDiagram) = parts(d,:V₂)

""" Convert a free diagram to a bipartite free diagram.

Reduce a free diagram to a free bipartite diagram with the same limit (the
default, `colimit=false`) or the same colimit (`colimit=true`). The reduction is
essentially the same in both cases, except for the choice of where to put
isolated vertices, where we follow the conventions described at
[`cone_objects`](@ref) and [`cocone_objects`](@ref). The resulting object is a
bipartite free diagram equipped with maps from the vertices of the bipartite
diagram to the vertices of the original diagram.
"""
function BipartiteFreeDiagram{Ob,Hom}(F::Functor{<:FinCat{Int}};
                                      colimit::Bool=false) where {Ob,Hom}
  d = FreeDiagramAsBipartite{Ob,Hom}()
  g = graph(dom(F))
  add_parts!(d, :V, nv(g))
  for v in vertices(g)
    x = ob_map(F, v)
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
    add_edge!(d, v₁, v₂, hom=hom_map(F, e))
  end
  return d
end
BipartiteFreeDiagram(F::Functor{<:FinCat{Int},<:Cat{Ob,Hom}}; kw...) where {Ob,Hom} =
  BipartiteFreeDiagram{Ob,Hom}(F; kw...)
  
end # module