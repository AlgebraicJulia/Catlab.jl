module BenchmarkGraphs

using BenchmarkTools
const SUITE = BenchmarkGroup(["c-sets", "graphs"])

using Catlab.Graphs

import LightGraphs
const LG = LightGraphs

# Graphs
########

graphs = SUITE["Graph"] = BenchmarkGroup()

graphs["make-path-graph"] = @benchmarkable begin
  g = Graph()
  add_vertices!(g, 10)
  add_edges!(g, 1:9, 2:10)
end

graphs["make-path-graph-lightgraphs"] = @benchmarkable begin
  g = LG.DiGraph()
  LG.add_vertices!(g, 10)
  for v in 1:9
    LG.add_edge!(g, v, v+1)
  end
end

end
