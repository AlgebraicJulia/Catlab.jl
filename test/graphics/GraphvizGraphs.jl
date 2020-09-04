module TestGraphvizGraphs
using Test
import JSON

using Catlab.CategoricalAlgebra.Graphs, Catlab.Graphics.GraphvizGraphs
import Catlab.Graphics: Graphviz

# Property graphs
#################

# Parsing
#--------

data_path(name::String) = joinpath(@__DIR__, "data", name)

# Undirected simple graph.
doc = open(JSON.parse, data_path("graphviz_graph.json"), "r")
parsed = parse_graphviz(doc)
@test parsed isa SymmetricPropertyGraph
@test nv(parsed) == 10
@test ne(parsed) ÷ 2 == 13

# Directed simple graph
doc = open(JSON.parse, data_path("graphviz_digraph.json"), "r")
parsed = parse_graphviz(doc)
@test parsed isa PropertyGraph
@test nv(parsed) == 5
@test src(parsed) == [1,1,1,2,3,4]
@test tgt(parsed) == [2,3,4,5,5,5]
@test get_vprop.([parsed], 1:nv(parsed), :name) == ["A", "B", "C", "D", "F"]
@test get_vprop(parsed, 1, :position) == [99, 162]
@test get_vprop(parsed, 1, :size) == [54, 36]
@test get_eprop(parsed, 1, :spline) isa Vector

# Visualizing
#------------

# Symmetric property graph.
g = SymmetricPropertyGraph{String}()
add_vertex!(g, label="v")
add_vertices!(g, 2)
add_edge!(g, 1, 2, xlabel="e")
gv = to_graphviz(g)
@test !gv.directed
nodes = filter(s -> s isa Graphviz.Node, gv.stmts)
edges = filter(s -> s isa Graphviz.Edge, gv.stmts)
@test length(nodes) == 3
@test length(edges) == 1
@test nodes[1].attrs[:label] == "v"
@test edges[1].attrs[:xlabel] == "e"

# Property graph.
g = PropertyGraph{String}()
add_vertices!(g, 3); add_edge!(g, 1, 2); add_edge!(g, 2, 3)
gv = to_graphviz(g)
@test gv.directed
@test length(filter(s -> s isa Graphviz.Node, gv.stmts)) == 3
@test length(filter(s -> s isa Graphviz.Edge, gv.stmts)) == 2

# Property graph with multiple edges.
g = PropertyGraph{String}()
add_vertices!(g, 2)
add_edge!(g, 1, 2, label="e1")
add_edge!(g, 1, 2, label="e2")
gv = to_graphviz(g)
@test gv.directed
nodes = filter(s -> s isa Graphviz.Node, gv.stmts)
edges = filter(s -> s isa Graphviz.Edge, gv.stmts)
@test length(nodes) == 2
@test length(edges) == 2
@test [ edge.attrs[:label] for edge in edges ] == ["e1", "e2"]

# Graphs
########

g = Graph(3)
add_edges!(g, [1,2], [2,3])
gv = to_graphviz(g)
@test gv.directed
nodes = filter(s -> s isa Graphviz.Node, gv.stmts)
@test [ node.attrs[:label] for node in nodes ] == ["", "", ""]

gv = to_graphviz(g, node_labels=true, edge_labels=true)
nodes = filter(s -> s isa Graphviz.Node, gv.stmts)
edges = filter(s -> s isa Graphviz.Edge, gv.stmts)
@test [ node.attrs[:label] for node in nodes ] == ["1", "2", "3"]
@test [ edge.attrs[:label] for edge in edges ] == ["1", "2"]

# Symmetric graphs
##################

g = SymmetricGraph(3)
add_edges!(g, [1,2], [2,3])
gv = to_graphviz(g, edge_labels=true)
@test !gv.directed
edges = filter(s -> s isa Graphviz.Edge, gv.stmts)
@test [ edge.attrs[:label] for edge in edges ] == ["(1,3)", "(2,4)"]

end
