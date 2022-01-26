# Benchmark Catlab.Graphs against LightGraphs and MetaGraphs.
using BenchmarkTools
const SUITE = BenchmarkGroup()

using Random
import LightGraphs, MetaGraphs
const LG, MG = LightGraphs, MetaGraphs

using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs
using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.WiringDiagrams: query
using Catlab.Programs: @relation

testdatadir = joinpath(dirname(@__FILE__), "..", "test", "testdata")

# Example Graphs
#
################

# Stolen from the Lightgraphs benchmark suite

dg1fn = joinpath(testdatadir, "graph-50-500.jgz")

LG_GRAPHS = Dict{String,LG.DiGraph}(
    "complete100"   => LG.complete_digraph(100),
    # "5000-50000"    => LG.loadgraph(dg1fn)["graph-5000-50000"],
    "path500"       => LG.path_digraph(500)
)

GRAPHS = Dict(k => from_lightgraph(g) for (k,g) in LG_GRAPHS)

LG_SYMGRAPHS = Dict{String,LG.Graph}(
    "complete100"   => LG.complete_graph(100),
    "tutte"         => LG.smallgraph(:tutte),
    "path500"       => LG.path_graph(500),
    # "5000-49947"    => LG.SimpleGraph(DIGRAPHS["5000-50000"])
)

SYMGRAPHS = Dict(k => from_lightgraph(g) for (k,g) in LG_SYMGRAPHS)

# Helpers
#########

# `bench_iter_edges` and `bench_has_edge` adapted from LightGraphs:
# https://github.com/JuliaGraphs/LightGraphs.jl/blob/master/benchmark/core.jl

function bench_iter_edges(g)
  count = 0
  for e in edges(g)
    s, t = src(g,e), tgt(g,e)
    count += 1
  end
  count
end
function bench_iter_edges_vectorized(g)
  count = 0
  for (s,t) in zip(src(g), tgt(g))
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

function bench_iter_neighbors(g)
  count = 0
  for v in vertices(g)
    count += length(neighbors(g,v))
  end
  count
end

@inline Graphs.nv(g::LG.AbstractGraph) = LG.nv(g)
@inline Graphs.vertices(g::LG.AbstractGraph) = LG.vertices(g)
@inline Graphs.edges(g::LG.AbstractGraph) = LG.edges(g)
@inline Graphs.src(g::LG.AbstractGraph, e::LG.AbstractEdge) = LG.src(e)
@inline Graphs.tgt(g::LG.AbstractGraph, e::LG.AbstractEdge) = LG.dst(e)
@inline Graphs.has_edge(g::LG.AbstractGraph, args...) = LG.has_edge(g, args...)
@inline Graphs.neighbors(g::LG.AbstractGraph, args...) = LG.neighbors(g, args...)

function Graphs.connected_component_projection(g::LG.AbstractGraph)
  label = Vector{Int}(undef, LG.nv(g))
  LG.connected_components!(label, g)
  normalize_labeling(label)
end

abstract type FindTrianglesAlgorithm end
struct TriangleBacktrackingSearch <: FindTrianglesAlgorithm end
struct TriangleQuery <: FindTrianglesAlgorithm end

""" Number of triangles in a graph.
"""
function ntriangles(g::T, ::TriangleBacktrackingSearch) where T
  triangle = T(3)
  add_edges!(triangle, [1,2,1], [2,3,3])
  length(homomorphisms(triangle, g, alg=BacktrackingSearch()))
end
function ntriangles(g, ::TriangleQuery)
  length(query(g, ntriangles_query))
end
const ntriangles_query = @relation (;) begin
  E(src=v1, tgt=v2)
  E(src=v2, tgt=v3)
  E(src=v1, tgt=v3)
end

# Graphs
########

bench = SUITE["Graph"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
clvecbench = bench["Catlab-vectorized"] = BenchmarkGroup()
lgbench = bench["LightGraphs"] = BenchmarkGroup()

n = 10000
clbench["make-path"] = @benchmarkable path_graph(Graph,n)
lgbench["make-path"] = @benchmarkable begin
  g = LG.DiGraph()
  LG.add_vertices!(g, n)
  for v in 1:(n-1)
    LG.add_edge!(g, v, v+1)
  end
end

g = path_graph(Graph, n)
lg = LG.DiGraph(g)

clbench["iter-edges"] = @benchmarkable bench_iter_edges($g)
clvecbench["iter-edges"] = @benchmarkable bench_iter_edges_vectorized($g)
lgbench["iter-edges"] = @benchmarkable bench_iter_edges($lg)
clbench["has-edge"] = @benchmarkable bench_has_edge($g)
lgbench["has-edge"] = @benchmarkable bench_has_edge($lg)
clbench["iter-neighbors"] = @benchmarkable bench_iter_neighbors($g)
lgbench["iter-neighbors"] = @benchmarkable bench_iter_neighbors($lg)


bench = SUITE["GraphConnComponents"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
lgbench = bench["LightGraphs"] = BenchmarkGroup()

n₀ = 2000
g₀ = path_graph(Graph, n₀)
g = ob(coproduct(fill(g₀, 5)))
lg = LG.DiGraph(g)
clbench["path-graph"] =
  @benchmarkable connected_component_projection_bfs($g)
lgbench["path-graph"] =
  @benchmarkable connected_component_projection($lg)

g₀ = star_graph(Graph, n₀)
g = ob(coproduct(fill(g₀, 5)))
lg = LG.DiGraph(g)
clbench["star-graph"] =
  @benchmarkable connected_component_projection_bfs($g)
lgbench["star-graph"] =
  @benchmarkable connected_component_projection($lg)

for gn in keys(GRAPHS)
  clbench[gn] = @benchmarkable connected_component_projection_bfs($(GRAPHS[gn]))
  lgbench[gn] = @benchmarkable connected_component_projection($(LG_GRAPHS[gn]))
end

bench = SUITE["GraphTriangles"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
lgbench = bench["LightGraphs"] = BenchmarkGroup()

n = 100
g = wheel_graph(Graph, n)
lg = LG.DiGraph(g)
clbench["wheel-graph-triangles-hom"] =
  @benchmarkable ntriangles($g, TriangleBacktrackingSearch())
clbench["wheel-graph-triangles"] =
  @benchmarkable ntriangles($g, TriangleQuery())

# Symmetric graphs
##################

bench = SUITE["SymmetricGraph"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
clvecbench = bench["Catlab-vectorized"] = BenchmarkGroup()
lgbench = bench["LightGraphs"] = BenchmarkGroup()

n = 10000
clbench["make-path"] = @benchmarkable path_graph(SymmetricGraph, n)
lgbench["make-path"] = @benchmarkable begin
  g = LG.Graph()
  LG.add_vertices!(g, n)
  for v in 1:(n-1)
    LG.add_edge!(g, v, v+1)
  end
end

g = path_graph(SymmetricGraph, n)
lg = LG.Graph(g)

clbench["iter-edges"] = @benchmarkable bench_iter_edges($g)
clvecbench["iter-edges"] = @benchmarkable bench_iter_edges_vectorized($g)
lgbench["iter-edges"] = @benchmarkable bench_iter_edges($lg)
clbench["has-edge"] = @benchmarkable bench_has_edge($g)
lgbench["has-edge"] = @benchmarkable bench_has_edge($lg)
clbench["iter-neighbors"] = @benchmarkable bench_iter_neighbors($g)
lgbench["iter-neighbors"] = @benchmarkable bench_iter_neighbors($lg)

bench = SUITE["SymmetricGraphConnComponent"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
lgbench = bench["LightGraphs"] = BenchmarkGroup()

n₀ = 2000
g₀ = path_graph(SymmetricGraph, n₀)
g = ob(coproduct(fill(g₀, 5)))
lg = LG.Graph(g)
clbench["path-graph-components"] =
  @benchmarkable connected_component_projection($g)
lgbench["path-graph-components"] =
  @benchmarkable connected_component_projection($lg)

g₀ = star_graph(SymmetricGraph, n₀)
g = ob(coproduct(fill(g₀, 5)))
lg = LG.Graph(g)
clbench["star-graph-components"] =
  @benchmarkable connected_component_projection($g)
lgbench["star-graph-components"] =
  @benchmarkable connected_component_projection($lg)

for gn in keys(SYMGRAPHS)
  clbench[gn] = @benchmarkable connected_component_projection_bfs($(SYMGRAPHS[gn]))
  lgbench[gn] = @benchmarkable connected_component_projection($(LG_SYMGRAPHS[gn]))
end

bench = SUITE["SymmetricGraphTriangles"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
lgbench = bench["LightGraphs"] = BenchmarkGroup()

n = 100
g = wheel_graph(SymmetricGraph, n)
lg = LG.Graph(g)
clbench["wheel-graph-triangles-hom"] =
  @benchmarkable ntriangles($g, TriangleBacktrackingSearch())
# clbench["wheel-graph-triangles-query"] =
clbench["wheel-graph-triangles"] =
  @benchmarkable ntriangles($g, TriangleQuery())
lgbench["wheel-graph-triangles"] = @benchmarkable sum(LG.triangles($lg))

# Weighted graphs
#################

bench = SUITE["WeightedGraph"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
clvecbench = bench["Catlab-vectorized"] = BenchmarkGroup()
lgbench = bench["MetaGraphs"] = BenchmarkGroup()

n = 10000
g = path_graph(WeightedGraph{Float64}, n; E=(weight=range(0,1,length=n-1),))
mg = MG.MetaDiGraph(g)

clvecbench["sum-weights"] = @benchmarkable sum(weight($g))
clbench["sum-weights"] = @benchmarkable begin
  total = 0.0
  for e in edges($g)
    total += weight($g, e)
  end
  total
end
lgbench["sum-weights"] = @benchmarkable begin
  total = 0.0
  for e in MG.edges($mg)
    total += MG.get_prop($mg, e, :weight)
  end
  total
end

clvecbench["increment-weights"] = @benchmarkable begin
  $g[:weight] .= $g[:weight] .+ 1.0
end

clbench["increment-weights"] = @benchmarkable begin
  for e in edges($g)
    $g[e,:weight] += 1.0
  end
end
lgbench["increment-weights"] = @benchmarkable begin
  for e in MG.edges($mg)
    MG.set_prop!($mg, e, :weight, MG.get_prop($mg, e, :weight) + 1.0)
  end
end

# Labeled graphs
################

bench = SUITE["LabeledGraph"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
lgbench = bench["LightGraphs"] = BenchmarkGroup()

@present TheoryLabeledGraph <: TheoryGraph begin
  Label::AttrType
  label::Attr(V,Label)
end
@acset_type LabeledGraph(TheoryLabeledGraph, index=[:src,:tgt]) <: AbstractGraph
@acset_type IndexedLabeledGraph(TheoryLabeledGraph, index=[:src,:tgt],
                                unique_index=[:label]) <: AbstractGraph

function discrete_labeled_graph(n::Int; indexed::Bool=false)
  g = (indexed ? IndexedLabeledGraph{String} : LabeledGraph{String})()
  add_vertices!(g, n, label=("v$i" for i in 1:n))
  g
end

function discrete_labeled_metagraph(n::Int; indexed::Bool=false)
  mg = MG.MetaDiGraph()
  for i in 1:n
    MG.add_vertex!(mg, :label, "v$i")
  end
  if indexed; MG.set_indexing_prop!(mg, :label) end
  mg
end

n = 5000
clbench["make-discrete"] = @benchmarkable discrete_labeled_graph($n)
lgbench["make-discrete"] = @benchmarkable discrete_labeled_metagraph($n)
clbench["make-discrete-indexed"] =
  @benchmarkable discrete_labeled_graph($n, indexed=true)
lgbench["make-discrete-indexed"] =
  @benchmarkable discrete_labeled_metagraph($n, indexed=true)

n = 10000
g = discrete_labeled_graph(n)
mg = discrete_labeled_metagraph(n)
clbench["iter-labels"] = @benchmarkable begin
  for v in vertices($g)
    label = $g[v,:label]
  end
end
lgbench["iter-labels"] = @benchmarkable begin
  for v in MG.vertices($mg)
    label = MG.get_prop($mg, v, :label)
  end
end

g = discrete_labeled_graph(n, indexed=true)
mg = discrete_labeled_metagraph(n, indexed=true)
Random.seed!(1)
σ = randperm(n)
clbench["indexed-lookup"] = @benchmarkable begin
  for i in $σ
    @assert incident($g, "v$i", :label) == i
  end
end
lgbench["indexed-lookup"] = @benchmarkable begin
  for i in $σ
    @assert $mg["v$i", :label] == i
  end
end

# Random Graphs
###############

bench = SUITE["RandomGraph"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
lgbench = bench["LightGraphs"] = BenchmarkGroup()

sizes = [10000]
ps = [0.001]
for size in sizes, p in ps
  clbench["erdos_renyi-$size-$p"] =
    @benchmarkable erdos_renyi($Graph, $size, $(p/2))
  lgbench["erdos_renyi-$size-$p"] =
    @benchmarkable LightGraphs.erdos_renyi($size, $p)
end

ks = [10]

for size in sizes, k in ks
  clbench["expected_degree_graph-$size-$k"] =
    @benchmarkable expected_degree_graph($Graph, $([min(k,size-1) for _ in 1:size]))
  lgbench["expected_degree_graph-$size-$k"] =
    @benchmarkable LightGraphs.expected_degree_graph($([min(k,size-1) for _ in 1:size]))
end

for size in sizes, k in ks
  clbench["watts_strogatz-$size-$k"] =
    @benchmarkable watts_strogatz($Graph, $size, $(min(k,size-1)), 0.5)
  lgbench["watts_strogatz-$size-$k"] =
    @benchmarkable LightGraphs.watts_strogatz($size, $(min(k,size-1)), 0.5)
end

# Searching
###########

bench = SUITE["Searching"] = BenchmarkGroup()
clbench = bench["Catlab"] = BenchmarkGroup()
lgbench = bench["LightGraphs"] = BenchmarkGroup()

for size in sizes, p in ps
  local g = erdos_renyi(Graph, size, p)
  local lg = LightGraphs.SimpleDiGraph(g)
  clbench["bfs_erdos_renyi-$size-$p"] = @benchmarkable bfs_parents($g,1)
  lgbench["bfs_erdos_renyi-$size-$p"] = @benchmarkable LightGraphs.bfs_parents($lg,1)
  clbench["dfs_erdos_renyi-$size-$p"] = @benchmarkable dfs_parents($g,1)
  lgbench["dfs_erdos_renyi-$size-$p"] = @benchmarkable LightGraphs.dfs_parents($lg,1)
end
