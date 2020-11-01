""" Algebras of the operads of wiring diagrams.
"""
module WiringDiagramAlgebras
export oapply

using Compat: isnothing

using ...CategoricalAlgebra
using ..UndirectedWiringDiagrams

# UWD algebra of structured multicospans
########################################

""" Compose structured multicospans according to UWD.

This function makes structured multicospans into an algebra of the operad of
undirected wiring diagrams.
"""
function oapply(composite::UndirectedWiringDiagram,
                cospans::AbstractVector{SCosp},
                junction_feet::Union{AbstractVector,Nothing}=nothing) where
    {Ob, Hom, Cosp <: Multicospan{Ob,<:AbstractVector{Hom}},
     L, SCosp <: StructuredMulticospan{L,Cosp}}
  @assert nboxes(composite) == length(cospans)
  if isnothing(junction_feet)
    junction_feet = Vector{dom(L)}(undef, njunctions(composite))
  else
    @assert njunctions(composite) == length(junction_feet)
  end

  # Create free diagram whose generating graph is a bipartite graph of the UWD's
  # boxes and junctions. Each directed edge goes from a junction vertex to a box
  # vertex, as defined by the UWD's junction map, and the edge is mapped to the
  # corresponding leg of a multicospan.
  diagram = FreeDiagram{Ob,Hom}()
  add_vertices!(diagram, nboxes(composite), ob=map(apex, cospans))
  jmap = add_vertices!(diagram, njunctions(composite))
  for (b, cospan) in zip(boxes(composite), cospans)
    for (p, leg, foot) in zip(ports(composite, b), legs(cospan), feet(cospan))
      j = junction(composite, p)
      add_edge!(diagram, jmap[j], b, hom=leg)
      if isassigned(junction_feet, j)
        foot′ = junction_feet[j]
        foot == foot′ || error(
          "Domains of structured cospans are not equal: $foot != $foot′")
      else
        junction_feet[j] = foot
      end
    end
  end
  set_subparts!(diagram, jmap, ob=map(L, junction_feet))

  # The composite multicospan is given by the colimit of this diagram.
  colim = colimit(diagram)
  outer_js = junction(composite, outer=true)
  outer_legs, outer_feet = legs(colim)[jmap[outer_js]], junction_feet[outer_js]
  StructuredMulticospan{L}(Multicospan(ob(colim), outer_legs), outer_feet)
end

end
