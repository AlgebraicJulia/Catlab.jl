module TestGraphGenerators
using Test

using Catlab.Graphs.BasicGraphs, Catlab.Graphs.GraphGenerators
using Catlab.CategoricalAlgebra: homomorphisms

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

# Star graphs
#------------

g = star_graph(Graph, n)
@test (nv(g), ne(g)) == (n, n-1)
@test length(unique(src(g,e) for e in edges(g))) == 1
g = star_graph(SymmetricGraph, n)
@test (nv(g), ne(g)) == (n, 2(n-1))

# Wheel graphs
#-------------

g = wheel_graph(Graph, n)
@test (nv(g), ne(g)) == (n, 2(n-1))
triangle = Graph(3)
add_edges!(triangle, [1,2,1], [2,3,3])
@test length(homomorphisms(triangle, g)) == n-1

g = wheel_graph(SymmetricGraph, n)
@test (nv(g), ne(g)) == (n, 4(n-1))
triangle = cycle_graph(SymmetricGraph, 3)
@test length(homomorphisms(triangle, g)) == 6(n-1) # == 3! * (n-1)

end
