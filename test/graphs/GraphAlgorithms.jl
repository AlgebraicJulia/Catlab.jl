module TestGraphAlgorithms
using Test

using Catlab.Graphs

# Connectivity
##############

g = Graph(6)
add_edges!(g, [2,3], [4,5])
@test connected_components(g) == [[1], [2,4], [3,5], [6]]

# Topological sorting
#####################

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

end
