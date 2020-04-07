#!/usr/bin/env julia

# Simple graphs
###############

run(pipeline(`dot -Tjson0 graphviz_digraph.dot`, stdout="graphviz_digraph.json"))
run(pipeline(`neato -Tjson0 graphviz_graph.dot`, stdout="graphviz_graph.json"))

# Wiring diagrams
#################

using Catlab.Graphics
using Catlab.Graphics.Graphviz: run_graphviz

diagram = include("graphviz_wiring_diagram.jl")
graph = to_graphviz(diagram)
open("graphviz_wiring_diagram.json", "w") do io
  run_graphviz(io, graph, format="json0")
end
