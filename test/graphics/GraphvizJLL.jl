module TestGraphvizJLL
using Test

import Catlab
using Catlab.Graphics.Graphviz
using Graphviz_jll
import JSON3

@test !isnothing(Base.get_extension(Catlab, :CatlabGraphvizExt))

graph = Graph("G",
  Node("n1"), Node("n2"), Node("n3"),
  Edge("n1","n2"), Edge("n2","n3"), Edge("n3","n1"))

# Hide any system Graphviz so that only the JLL binaries can be used.
withenv("PATH" => nothing) do
  # Omit `sfdp`: Graphviz_jll is built without the triangulation library that
  # `sfdp` needs for its default overlap removal.
  for prog in ("dot", "neato", "fdp", "twopi", "circo")
    svg = sprint(io -> run_graphviz(io, graph; prog=prog, format="svg"))
    @test occursin("<svg", svg)
  end

  # JSON output, as used by `graphviz_layout` for wiring diagrams.
  doc = JSON3.read(run_graphviz(graph, format="json0"))
  @test length(doc["objects"]) == 3
end

end
