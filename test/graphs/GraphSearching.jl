module TestGraphSearching

using Test

using ACSets: @acset

using Catlab.Graphs.BasicGraphs, Catlab.Graphs.GraphSearching
using Catlab.Graphs.GraphSearching: tree
using Catlab.CategoricalAlgebra: is_isomorphic

# BFS
#----

g = Graph(4)
add_edges!(g, [1,2,1,3], [2,3,3,4])
z = @inferred(bfs_tree(g, 1))
t = bfs_parents(g, 1)
@test t == [1,1,1,3]
@test nv(z) == 4 && ne(z) == 3 && !has_edge(z,2,3)

g = Graph(5) # house graph
add_edges!(g, [1,1,2,3,3,4], [2,3,4,4,5,5])
n = nv(g)
parents = bfs_parents(g, 1)
@test length(parents) == n
t1 = @inferred(bfs_tree(g, 1))
t2 = tree(parents)
@test t1 == t2
@test t2 isa AbstractGraph
@test ne(t2) < nv(t2)

# DFS
#----

g = Graph(4)
add_edges!(g, [1,2,1,3], [2,3,3,4])
z = @inferred(dfs_tree(g, 1))
@test ne(z) == 3 && nv(z) == 4
@test !has_edge(z, 1, 3)

# Trees
#------

g = tree([1, 1, 1, 2, 2])
g′ = @acset Graph begin
  V = 5
  E = 4
  src = [1, 1, 2, 2]
  tgt = [2, 3, 4, 5]
end

@test is_isomorphic(g, g′)

end
