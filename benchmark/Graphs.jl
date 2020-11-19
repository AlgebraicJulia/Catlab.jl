""" Benchmark Catlab.Graphs against LightGraphs and MetaGraphs.
"""
module BenchmarkGraphs

using BenchmarkTools
const SUITE = BenchmarkGroup()

using Random
import LightGraphs, MetaGraphs
const LG, MG = LightGraphs, MetaGraphs

using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs

# Helpers
#########

# `bench_iter_edges` and `bench_has_edge` adapted from LightGraphs:
# https://github.com/JuliaGraphs/LightGraphs.jl/blob/master/benchmark/core.jl

function bench_iter_edges(g::Union{AbstractGraph,AbstractSymmetricGraph})
  count = 0
  for (s,t) in zip(src(g), tgt(g))
    count += 1
  end
  count
end
function bench_iter_edges(g::LG.AbstractGraph)
  count = 0
  for e in LG.edges(g)
    s, t = LG.src(e), LG.dst(e)
    count += 1
  end
  count
end

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

@inline Graphs.nv(g::LG.AbstractGraph) = LG.nv(g)
@inline Graphs.has_edge(g::LG.AbstractGraph, args...) = LG.has_edge(g, args...)

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
lg = LG.DiGraph(g)

bench["iter-edges"] = @benchmarkable bench_iter_edges($g)
bench["iter-edges-lightgraphs"] = @benchmarkable bench_iter_edges($lg)
bench["has-edge"] = @benchmarkable bench_has_edge($g)
bench["has-edge-lightgraphs"] = @benchmarkable bench_has_edge($lg)

v = n÷2
bench["inneighbors"] = @benchmarkable inneighbors($g, $v)
bench["outneighbors"] = @benchmarkable outneighbors($g, $v)
bench["inneighbors-lightgraphs"] = @benchmarkable LG.inneighbors($lg, $v)
bench["outneighbors-lightgraphs"] = @benchmarkable LG.outneighbors($lg, $v)

n₀ = 50
g₀ = Graph(n₀)
add_edges!(g₀, 1:(n₀-1), 2:n₀)
g = ob(coproduct(fill(g, 5)))
lg = LG.DiGraph(g)
bench["path-graph-components"] = @benchmarkable connected_components($g)
bench["path-graph-components-proj"] =
  @benchmarkable connected_component_projection($g)
bench["path-graph-components-lightgraphs"] =
  @benchmarkable LG.weakly_connected_components($lg)

g₀ = Graph(n₀)
add_edges!(g₀, fill(1,n₀-1), 2:n₀)
g = ob(coproduct(fill(g, 5)))
lg = LG.DiGraph(g)
bench["star-graph-components"] = @benchmarkable connected_components($g)
bench["star-graph-components-proj"] =
  @benchmarkable connected_component_projection($g)
bench["star-graph-components-lightgraphs"] =
  @benchmarkable LG.weakly_connected_components($lg)

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
lg = LG.Graph(g)

bench["iter-edges"] = @benchmarkable bench_iter_edges($g)
bench["iter-edges-lightgraphs"] = @benchmarkable bench_iter_edges($lg)
bench["has-edge"] = @benchmarkable bench_has_edge($g)
bench["has-edge-lightgraphs"] = @benchmarkable bench_has_edge($lg)

v = n÷2
bench["neighbors"] = @benchmarkable neighbors($g, $v)
bench["neighbors-lightgraphs"] = @benchmarkable LG.neighbors($lg, $v)

n₀ = 50
g₀ = SymmetricGraph(n₀)
add_edges!(g₀, 1:(n₀-1), 2:n₀)
g = ob(coproduct(fill(g, 5)))
lg = LG.Graph(g)
bench["path-graph-components"] = @benchmarkable connected_components($g)
bench["path-graph-components-proj"] =
  @benchmarkable connected_component_projection($g)
bench["path-graph-components-lightgraphs"] =
  @benchmarkable LG.connected_components($lg)

g₀ = SymmetricGraph(n₀)
add_edges!(g₀, fill(1,n₀-1), 2:n₀)
g = ob(coproduct(fill(g, 5)))
lg = LG.Graph(g)
bench["star-graph-components"] = @benchmarkable connected_components($g)
bench["star-graph-components-proj"] =
  @benchmarkable connected_component_projection($g)
bench["star-graph-components-lightgraphs"] =
  @benchmarkable LG.connected_components($lg)

# Weighted graphs
#################

bench = SUITE["WeightedGraph"] = BenchmarkGroup()

n = 500
g = WeightedGraph{Float64}(n)
add_edges!(g, 1:(n-1), 2:n, weight=range(0, 1, length=n-1))
mg = MG.MetaDiGraph(g)

bench["sum-weights"] = @benchmarkable sum(weight($g))
bench["sum-weights-slow"] = @benchmarkable begin
  # Slower than above but useful for comparison with MetaGraphs.
  total = 0.0
  for e in edges($g)
    total += weight($g, e)
  end
  total
end
bench["sum-weights-metagraphs"] = @benchmarkable begin
  total = 0.0
  for e in MG.edges($mg)
    total += MG.get_prop($mg, e, :weight)
  end
  total
end

end
