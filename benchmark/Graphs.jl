module BenchmarkGraphs

using BenchmarkTools
const SUITE = BenchmarkGroup()

using Random
import LightGraphs
const LG = LightGraphs

using Catlab.Graphs

# Benchmarks adapted from LightGraphs
# https://github.com/JuliaGraphs/LightGraphs.jl/blob/master/benchmark/core.jl

@inline Graphs.nv(g::LG.AbstractGraph) = LG.nv(g)
@inline Graphs.has_edge(g::LG.AbstractGraph, args...) = LG.has_edge(g, args...)

function bench_has_edge(g)
  Random.seed!(1)
  n = nv(g)
  srcs, tgts = rand(1:n, n÷4), rand(1:n, n÷4)
  count = 0
  for (s, t) in zip(srcs, tgts)
    if has_edge(g, s, t)
      count += 1
    end
  end
  count
end

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

g = Graph(n)
add_edges!(g, 1:(n-1), 2:n)
bench["has-edge"] = @benchmarkable bench_has_edge($g)

lg = LG.DiGraph(g)
bench["has-edge-lightgraphs"] = @benchmarkable bench_has_edge($lg)

v = n÷2
bench["inneighbors"] = @benchmarkable inneighbors($g, $v)
bench["outneighbors"] = @benchmarkable outneighbors($g, $v)
bench["inneighbors-lightgraphs"] = @benchmarkable LG.inneighbors($lg, $v)
bench["outneighbors-lightgraphs"] = @benchmarkable LG.outneighbors($lg, $v)

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

g = SymmetricGraph(n)
add_edges!(g, 1:(n-1), 2:n)
bench["has-edge"] = @benchmarkable bench_has_edge($g)

lg = LG.Graph(g)
bench["has-edge-lightgraphs"] = @benchmarkable bench_has_edge($lg)

v = n÷2
bench["neighbors"] = @benchmarkable neighbors($g, $v)
bench["neighbors-lightgraphs"] = @benchmarkable LG.neighbors($lg, $v)

end
