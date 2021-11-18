module TestGraphAlgorithms
using Test

using Catlab.Graphs

# Connectivity
##############

g = Graph(6)
add_edges!(g, [2,3], [4,5])
@test connected_components(g) == [[1], [2,4], [3,5], [6]]

# DAGs
######

# Topological sorting
#--------------------

# Discrete graph.
g = Graph(5)
@test topological_sort(g) == 1:5

# Path graph.
g = Graph(5)
add_edges!(g, 5:-1:2, 4:-1:1)
@test topological_sort(g) == 5:-1:1

# Diamond.
g = Graph(4)
add_edges!(g, [1,1,2,3], [2,3,4,4])
@test topological_sort(g) == 1:4

# Multiple edges.
g = Graph(3)
add_edges!(g, [1,1,1,2], [2,2,3,3])
@test topological_sort(g) == 1:3

# Error handling: cyclic graph.
g = Graph(3)
add_edges!(g, [1,2,3], [2,3,1])
@test_throws Exception topological_sort(g)

# Transitivity
#-------------

g = Graph(3)
add_edges!(g, [1,2], [2,3])
g₀ = copy(g)
@test transitive_reduction!(g) == g₀
add_edge!(g, 1, 3)
@test transitive_reduction!(g) == g₀

g = Graph(5)
add_edges!(g, [1,1,1,1,2,3,3,4], [2,3,4,5,4,4,5,5])
transitive_reduction!(g)
@test sort!(collect(zip(src(g), tgt(g)))) == [(1,2),(1,3),(2,4),(3,4),(4,5)]

# Enumerating paths
g = Graph(3)
add_edges!(g, [1,2,2], [2,3,3])

ep = enumerate_paths(g)
@test all([length(ep[i=>i]) == 1 for i in vertices(g)])
@test length(ep[1=>2]) == 1
@test length(ep[1=>3]) == 2
@test length(ep[2=>1]) == 0

end
