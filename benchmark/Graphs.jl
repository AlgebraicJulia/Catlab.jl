module BenchmarkGraphs

using BenchmarkTools
const SUITE = BenchmarkGroup(["c-sets", "graphs"])

using Catlab.Graphs

import LightGraphs
const LG = LightGraphs

# Graphs
########

bench = SUITE["Graph"] = BenchmarkGroup()

n = 500
bench["make-path"] = @benchmarkable begin
  g = Graph()
  add_vertices!(g, n)
  add_edges!(g, 1:(n-1), 2:n)
end

bench["make-path-lightgraphs"] = @benchmarkable begin
  g = LG.DiGraph()
  LG.add_vertices!(g, n)
  for v in 1:(n-1)
    LG.add_edge!(g, v, v+1)
  end
end

g = Graph(5)
add_edges!(g, [1,2,3,3], [3,3,4,5])
bench["inneighbors"] = @benchmarkable inneighbors($g, 3)
bench["outneighbors"] = @benchmarkable outneighbors($g, 3)

lg = LG.DiGraph(g)
bench["inneighbors-lightgraphs"] = @benchmarkable LG.inneighbors($lg, 3)
bench["outneighbors-lightgraphs"] = @benchmarkable LG.outneighbors($lg, 3)

# Symmetric graphs
##################

bench = SUITE["SymmetricGraph"] = BenchmarkGroup()

n = 500
bench["make-path"] = @benchmarkable begin
  g = SymmetricGraph()
  add_vertices!(g, n)
  add_edges!(g, 1:(n-1), 2:n)
end

bench["make-path-lightgraphs"] = @benchmarkable begin
  g = LG.Graph()
  LG.add_vertices!(g, n)
  for v in 1:(n-1)
    LG.add_edge!(g, v, v+1)
  end
end

g = SymmetricGraph(5)
add_edges!(g, [1,2,3,3], [3,3,4,5])
bench["neighbors"] = @benchmarkable neighbors($g, 3)

lg = LG.Graph(g)
bench["neighbors-lightgraphs"] = @benchmarkable LG.neighbors($lg, 3)

end
