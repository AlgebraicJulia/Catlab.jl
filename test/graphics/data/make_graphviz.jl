#!/usr/bin/env julia

# Simple graphs
###############

run(pipeline(`dot -Tjson0 graphviz_digraph.dot`, stdout="graphviz_digraph.json"))
run(pipeline(`neato -Tjson0 graphviz_graph.dot`, stdout="graphviz_graph.json"))

# Wiring diagrams
#################

using Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.Graphics.Graphviz: run_graphviz

f = singleton_diagram(Box(:f, [:A], [:A]))
g = singleton_diagram(Box(:g, [:B], [:B]))
h = singleton_diagram(Box(:h, [:A, :B], [:C]))
diagram = compose(otimes(f,g),h)

graph = to_graphviz(diagram)
open("graphviz_wiring_diagram.json", "w") do io
  run_graphviz(io, graph, format="json0")
end
