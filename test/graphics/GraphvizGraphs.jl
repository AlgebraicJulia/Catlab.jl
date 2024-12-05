module TestGraphvizGraphs
using Test
import JSON3

using Catlab.Theories, Catlab.Graphs, Catlab.Graphics.GraphvizGraphs
import Catlab.Graphics: Graphviz
using Catlab.CategoricalAlgebra.Subobjects
using Catlab.CategoricalAlgebra.CSets
using Catlab.CategoricalAlgebra.FinSets

const stmts = Graphviz.filter_statements

# Property graphs
#################

# Parsing
#--------

data_path(name::String) = joinpath(@__DIR__, "data", name)

# Undirected simple graph.
doc = open(JSON3.read, data_path("graphviz_graph.json"), "r")
parsed = parse_graphviz(doc)
@test parsed isa SymmetricPropertyGraph
@test nv(parsed) == 10
@test ne(parsed) ÷ 2 == 13

# Directed simple graph
doc = open(JSON3.read, data_path("graphviz_digraph.json"), "r")
parsed = parse_graphviz(doc)
@test parsed isa PropertyGraph
@test nv(parsed) == 5
@test src(parsed) == [1,1,1,2,3,4]
@test tgt(parsed) == [2,3,4,5,5,5]
@test get_vprop.([parsed], 1:nv(parsed), :name) == ["A", "B", "C", "D", "F"]
@test get_vprop(parsed, 1, :position) == [99, 162]
@test get_vprop(parsed, 1, :size) == [54, 36]
@test get_eprop(parsed, 1, :spline) isa Vector

# Visualizion
#------------

# Symmetric property graph.
g = SymmetricPropertyGraph{String}()
add_vertex!(g, label="v")
add_vertices!(g, 2)
add_edge!(g, 1, 2, xlabel="e")
gv = to_graphviz(g)
@test !gv.directed
@test length(stmts(gv, Graphviz.Node)) == 3
@test length(stmts(gv, Graphviz.Edge)) == 1
@test stmts(gv, Graphviz.Node, :label) == ["v"]
@test stmts(gv, Graphviz.Edge, :xlabel) == ["e"]

# Property graph.
g = PropertyGraph{String}()
add_vertices!(g, 3); add_edge!(g, 1, 2); add_edge!(g, 2, 3)
gv = to_graphviz(g)
@test gv.directed
@test length(stmts(gv, Graphviz.Node)) == 3
@test length(stmts(gv, Graphviz.Edge)) == 2

# Property graph with multiple edges.
g = PropertyGraph{String}()
add_vertices!(g, 2)
add_edge!(g, 1, 2, label="e1")
add_edge!(g, 1, 2, label="e2")
gv = to_graphviz(g)
@test gv.directed
@test length(stmts(gv, Graphviz.Node)) == 2
@test length(stmts(gv, Graphviz.Edge)) == 2
@test stmts(gv, Graphviz.Edge, :label) == ["e1", "e2"]

# Graphs
########

g = path_graph(Graph, 3)
gv = to_graphviz(g)
@test gv.directed
@test stmts(gv, Graphviz.Node, :label) == fill("", 3)

g = path_graph(LabeledGraph{Symbol}, 3, V=(label=[:x, :y, :z],))
gv = to_graphviz(g, node_labels=:label)
@test stmts(gv, Graphviz.Node, :label) == ["x", "y", "z"]

g = path_graph(LabeledGraph{Tuple}, 3, V=(label=[("1",), ("2",), ("3",)],))
gv = to_graphviz(g, node_labels=:label)
@test stmts(gv, Graphviz.Node, :label) == ["1", "2", "3"]

g = path_graph(LabeledGraph{Tuple}, 3, V=(label=[("1", "a"), ("2", "b"), ("3", "c")],))
gv = to_graphviz(g, node_labels=:label)
@test stmts(gv, Graphviz.Node, :label) == ["1,a", "2,b", "3,c"]

g = path_graph(LabeledGraph{Tuple}, 3, V=(label=[("1", :a), ("2", :b), ("3", :c)],))
gv = to_graphviz(g, node_labels=:label)
@test stmts(gv, Graphviz.Node, :label) == ["1,a", "2,b", "3,c"]

g = path_graph(NamedGraph{Symbol,Symbol}, 3,
               V=(vname=[:x,:y,:z],), E=(ename=[:f,:g],))
gv = to_graphviz(g, node_labels=true, edge_labels=true)
@test stmts(gv, Graphviz.Node, :label) == ["x", "y", "z"]
@test stmts(gv, Graphviz.Edge, :label) == ["f", "g"]

g = path_graph(WeightedGraph{Float64}, 3, E=(weight=[0.5, 1.5],))
gv = to_graphviz(g, edge_labels=:weight)
@test stmts(gv, Graphviz.Edge, :label) == ["0.5", "1.5"]

@present SchEdgeLabeledGraph <: SchLabeledGraph begin
    Edge_Label::AttrType
    edge_label::Attr(E,Edge_Label)
end

@acset_type EdgeLabeledGraph(SchEdgeLabeledGraph, index=[:src,:tgt]) <: AbstractLabeledGraph

g = @acset EdgeLabeledGraph{Tuple, Tuple} begin
    V = 2
    label = [("a", "1"), ("b", "2")]
end

gv = to_graphviz(g, node_labels=:label)
@test stmts(gv, Graphviz.Node, :label) == ["a,1", "b,2"]

add_edges!(g, [1], [2], edge_label = [("a", "1")])

gv = to_graphviz(g, edge_labels=:edge_label, node_labels=:label)
@test stmts(gv, Graphviz.Edge, :label) == ["a,1"]

# Symmetric graphs
##################

g = path_graph(SymmetricGraph, 3)
gv = to_graphviz(g, edge_labels=true)
@test !gv.directed
@test stmts(gv, Graphviz.Node, :label) == fill("", 3)
@test stmts(gv, Graphviz.Edge, :label) == ["(1,3)", "(2,4)"]

g = path_graph(SymmetricWeightedGraph{Float64}, 3, E=(weight=[0.5, 1.5],))
gv = to_graphviz(g, edge_labels=:weight)
@test stmts(gv, Graphviz.Edge, :label) == ["0.5", "1.5"]

# Reflexive graphs
##################

g = path_graph(ReflexiveGraph, 3)
gv = to_graphviz(g, show_reflexive=false)
@test gv.directed
@test length(stmts(gv, Graphviz.Node)) == 3
@test length(stmts(gv, Graphviz.Edge)) == 2

gv = to_graphviz(g, edge_labels=true, show_reflexive=true)
@test length(stmts(gv, Graphviz.Edge)) == 5
@test stmts(gv, Graphviz.Edge, :label) == ["1", "2", "3", "4", "5"]
@test stmts(gv, Graphviz.Edge, :style) == fill("dashed", 3)

# Symmetric reflexive graphs
############################

g = path_graph(SymmetricReflexiveGraph, 3)
gv = to_graphviz(g, show_reflexive=false)
@test !gv.directed
@test length(stmts(gv, Graphviz.Node)) == 3
@test length(stmts(gv, Graphviz.Edge)) == 2

gv = to_graphviz(g, edge_labels=true, show_reflexive=true)
@test length(stmts(gv, Graphviz.Edge)) == 5
@test stmts(gv, Graphviz.Edge, :label) == ["1", "2", "3", "(4,6)", "(5,7)"]
@test stmts(gv, Graphviz.Edge, :style) == fill("dashed", 3)

# Half-edge graphs
##################

g = path_graph(HalfEdgeGraph, 3)
gv = to_graphviz(g, edge_labels=true)
@test !gv.directed
@test stmts(gv, Graphviz.Node, :label) == fill("", 3)
@test stmts(gv, Graphviz.Edge, :label) == ["(1,3)", "(2,4)"]

g = HalfEdgeGraph(2)
add_edge!(g, 1, 2)
add_dangling_edges!(g, [1,2])
gv = to_graphviz(g, node_labels=true, edge_labels=true)
@test stmts(gv, Graphviz.Node, :label) == ["1", "2", "", ""]
@test stmts(gv, Graphviz.Edge, :label) == ["(1,2)", "3", "4"]

# Subgraphs
###########

g = path_graph(Graph, 3)
subgraph = Subobject(g, V=[2,3], E=[1])
gv = to_graphviz(subgraph)
@test length(stmts(gv, Graphviz.Node)) == 3
@test length(stmts(gv, Graphviz.Edge)) == 2
@test length(stmts(gv, Graphviz.Node, :color)) == 2
@test length(stmts(gv, Graphviz.Edge, :color)) == 1

# Bipartite graphs
##################

g = UndirectedBipartiteGraph(3, 4)
add_edges!(g, [1,1,3], [1,4,2])
gv = to_graphviz(g, invis_edges=true)
@test length(stmts(gv, Graphviz.Subgraph)) == 2
@test length(stmts(gv, Graphviz.Edge)) == ne(g)
gv1, gv2 = stmts(gv, Graphviz.Subgraph)
@test length(stmts(gv1, Graphviz.Node)) == nv₁(g)
@test length(stmts(gv2, Graphviz.Node)) == nv₂(g)
@test length(stmts(gv1, Graphviz.Edge)) == nv₁(g) - 1
@test length(stmts(gv2, Graphviz.Edge)) == nv₂(g) - 1

g = BipartiteGraph(3, 4)
add_edges₁₂!(g, [1,1,3], [1,4,2])
add_edges₂₁!(g, 1:4, [1,2,2,3])
gv = to_graphviz(g, invis_edges=true)
@test length(stmts(gv, Graphviz.Subgraph)) == 2
@test length(stmts(gv, Graphviz.Edge)) == ne₁₂(g) + ne₂₁(g)

# Graph homomorphisms
#####################

# test we only get 1 subgraph with empty function
f = delete(Graph())
gv = to_graphviz(f, draw_codom=true)
@test gv.directed
@test length(stmts(gv, Graphviz.Subgraph)) == 1

# homomorphism between graphs with edges
A = Graph(3)
add_edges!(A, [1,1], [2,3])
B = Graph(4)
add_edges!(B, [1,3], [2,4])
f = ACSetTransformation(A, B; V = [1,2,2], E = [1,1])

gv = to_graphviz(f, draw_codom=true)
@test gv.directed
@test length(stmts(gv, Graphviz.Subgraph)) == 2

# Functions between finite sets
###############################

A = FinSet(4)
B = FinSet(3)
f = FinFunction([1,3,2,2], A, B)

fv = to_graphviz(f, graph_attrs=Dict(:splines=>"false"))
@test length(stmts(fv, Graphviz.Subgraph)) == 2
fv1, fv2 = stmts(fv, Graphviz.Subgraph)

@test length(stmts(fv1, Graphviz.Edge)) == length(A) - 1
@test length(stmts(fv2, Graphviz.Edge)) == length(B) - 1
@test length(stmts(fv, Graphviz.Edge)) == 4
@test length(stmts(fv1, Graphviz.Node)) == length(A)
@test length(stmts(fv2, Graphviz.Node)) == length(B)

end
