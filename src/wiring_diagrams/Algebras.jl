""" Algebras of the operads of wiring diagrams.
"""
module WiringDiagramAlgebras

using ...CategoricalAlgebra
using ..UndirectedWiringDiagrams

# UWD algebra of structured multicospans
########################################

""" Compose structured multicospans according to undirected wiring diagram.

In this way, structured multicospans are an algebra of the operad of UWDs.
"""
function (composite::UndirectedWiringDiagram)(cospans::AbstractVector{SCosp}) where
    {Ob, Hom, Cosp <: Multicospan{Ob,<:AbstractVector{Hom}},
     L, SCosp <: StructuredMulticospan{L,Cosp}}
  # Create free diagram whose generating graph is a bipartite graph of the UWD's
  # boxes and junctions. Each directed edge goes from a junction vertex to a box
  # vertex, as defined by the UWD's junction map, and the edge is mapped to the
  # corresponding leg of a multicospan.
  @assert nboxes(composite) == length(cospans)
  diagram = FreeDiagram{Ob,Hom}()
  add_vertices!(diagram, nboxes(composite), ob=map(apex, cospans))
  jmap = add_vertices!(diagram, njunctions(composite))
  for (box, cospan) in zip(boxes(composite), cospans)
    for (port, leg) in zip(ports(composite, box), legs(cospan))
      j = jmap[junction(composite, port)]
      add_edge!(diagram, j, box, hom=leg)
      set_subparts!(diagram, j, ob=dom(leg))
    end
  end

  # The composite multicospan is given by the colimit of this diagram.
  colim = colimit(diagram)
  outer_legs = legs(colim)[jmap[junction(composite, outer=true)]]
  cospan = Multicospan(ob(colim), outer_legs)
  feet = [ right(L, dom(leg)) for leg in outer_legs ]
  StructuredMulticospan{L}(cospan, feet)
end

end
