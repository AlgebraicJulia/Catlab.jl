module TestGraphGenerators
using Test

using Catlab.Graphs.BasicGraphs, Catlab.Graphs.GraphGenerators

# Path graphs
#------------

n = 5
g = path_graph(Graph, n)
@test (nv(g), ne(g)) == (n, n-1)
g = path_graph(SymmetricGraph, n)
@test (nv(g), ne(g)) == (n, 2(n-1))

# Cycle graphs
#-------------

n = 5
g = cycle_graph(Graph, n)
@test (nv(g), ne(g)) == (n, n)
g = cycle_graph(SymmetricGraph, n)
@test (nv(g), ne(g)) == (n, 2n)

end
