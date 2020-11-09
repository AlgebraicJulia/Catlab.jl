module TestGraphAlgorithms
using Test

using Catlab.Graphs

# Connectivity
##############

g = Graph(6)
add_edges!(g, [2,3], [4,5])
@test connected_components(g) == [[1], [2,4], [3,5], [6]]

end
