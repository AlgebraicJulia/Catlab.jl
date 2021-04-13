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

g = cycle_graph(Graph, n)
@test (nv(g), ne(g)) == (n, n)
g = cycle_graph(SymmetricGraph, n)
@test (nv(g), ne(g)) == (n, 2n)

# Complete graphs
#----------------

for T in (Graph, SymmetricGraph)
  g = complete_graph(T, n)
  @test (nv(g), ne(g)) == (n, n*(n-1))
end
for T in (ReflexiveGraph, SymmetricReflexiveGraph)
  g = complete_graph(T, n)
  @test (nv(g), ne(g)) == (n, n*n)
end

end
