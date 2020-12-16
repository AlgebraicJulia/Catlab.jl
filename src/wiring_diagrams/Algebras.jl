""" Algebras of operads of wiring diagrams.
"""
module WiringDiagramAlgebras
export oapply

using Compat: isnothing

using ...Theories, ...CategoricalAlgebra
using ..UndirectedWiringDiagrams

""" Compose morphisms according to UWD.

The morphisms corresponding to the boxes, and optionally also the objects
corresponding to the junctions, are given by dictionaries indexed by
box/junction attributes. The default attributes are those compatible with the
`@relation` macro.
"""
function oapply(composite::UndirectedWiringDiagram, hom_map::AbstractDict,
                ob_map::Union{AbstractDict,Nothing}=nothing;
                hom_attr::Symbol=:name, ob_attr::Symbol=:variable)
  homs = [ hom_map[name] for name in subpart(composite, hom_attr) ]
  obs = isnothing(ob_map) ? nothing :
    [ ob_map[name] for name in subpart(composite, ob_attr) ]
  oapply(composite, homs, obs)
end

# Structured multicospans
#########################

""" Compose structured multicospans according to UWD.

This function makes structured multicospans into an algebra of the operad of
undirected wiring diagrams.
"""
function oapply(composite::UndirectedWiringDiagram,
                cospans::AbstractVector{<:StructuredMulticospan{L}},
                junction_feet::Union{AbstractVector,Nothing}=nothing) where L
  @assert nboxes(composite) == length(cospans)
  if isnothing(junction_feet)
    junction_feet = Vector{first(dom(L))}(undef, njunctions(composite))
  else
    @assert njunctions(composite) == length(junction_feet)
  end

  # Create bipartite free diagram whose vertices of types 1 and 2 are the UWD's
  # junctions and boxes, respectively, and whose edges are define by the UWD's
  # junction map.
  diagram = BipartiteFreeDiagram{codom(L)...}()
  add_vertices₁!(diagram, njunctions(composite))
  add_vertices₂!(diagram, nboxes(composite), ob₂=map(apex, cospans))
  for (b, cospan) in zip(boxes(composite), cospans)
    for (p, leg, foot) in zip(ports(composite, b), legs(cospan), feet(cospan))
      j = junction(composite, p)
      add_edge!(diagram, j, b, hom=leg)
      if isassigned(junction_feet, j)
        foot′ = junction_feet[j]
        foot == foot′ || error(
          "Domains of structured cospans are not equal: $foot != $foot′")
      else
        junction_feet[j] = foot
      end
    end
  end
  diagram[:ob₁] = map(L, junction_feet)

  # Find, or if necessary create, an outgoing edge for each junction. The
  # existence of such edges is an assumption for colimits of bipartite diagrams.
  # The edges are also needed to construct inclusions for the outer junctions.
  junction_edges = map(junctions(composite)) do j
    out_edges = incident(diagram, j, :src)
    if isempty(out_edges)
      x = ob₁(diagram, j)
      v = add_vertex₂!(diagram, ob₂=x)
      add_edge!(diagram, j, v, hom=id(x))
    else
      first(out_edges)
    end
  end

  # The composite multicospan is given by the colimit of this diagram.
  colim = colimit(diagram)
  outer_js = junction(composite, outer=true)
  outer_legs = map(junction_edges[outer_js]) do e
    hom(diagram, e) ⋅ legs(colim)[tgt(diagram, e)]
  end
  outer_feet = junction_feet[outer_js]
  StructuredMulticospan{L}(Multicospan(ob(colim), outer_legs), outer_feet)
end

end
