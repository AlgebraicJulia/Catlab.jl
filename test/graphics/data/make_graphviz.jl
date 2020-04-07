#!/usr/bin/env julia

# Simple graphs
###############

run(pipeline(`dot graphviz_digraph.dot -Tjson0`, stdout="graphviz_digraph.json"))
run(pipeline(`neato graphviz_graph.dot -Tjson0`, stdout="graphviz_graph.json"))

# Wiring diagrams
#################

using Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.Graphics.Graphviz: run_graphviz

f = singleton_diagram(Box(:f, [:A], [:A]))
g = singleton_diagram(Box(:g, [:B], [:B]))
h = singleton_diagram(Box(:h, [:A, :B], [:C]))
diagram = compose(otimes(f,g),h)

graph = to_graphviz(diagram)
json = run_graphviz(graph, format="json0")
open("graphviz_wiring_diagram.json", "w") do io
  write(io, json)
end
