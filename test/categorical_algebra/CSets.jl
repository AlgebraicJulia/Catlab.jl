module TestCSets
using Test

using LightGraphs

using Catlab: @present
using Catlab.Theories: Category, FreeCategory
using Catlab.CategoricalAlgebra.CSets

# C-sets
########

# Discrete dynamical systems as a simple example of C-sets.

@present TheoryDDS(FreeCategory) begin
  X::Ob
  Φ::Hom(X,X)
end

const DDS = CSetType(TheoryDDS)

dds = DDS()
@test nparts(dds, :X) == 0
@test add_part!(dds, :X) == 1
@test nparts(dds, :X) == 1
@test incident(dds, 1, :Φ) == []

set_subpart!(dds, 1, :Φ, 1)
@test subpart(dds, 1, :Φ) == 1
@test incident(dds, 1, :Φ) == [1]

@test add_part!(dds, :X, (Φ=1,)) == 2
@test add_part!(dds, :X, (Φ=1,)) == 3
@test subpart(dds, [2,3], :Φ) == [1,1]
@test incident(dds, 1, :Φ) == [1,2,3]

# Graphs
########

g = CSets.Graph()
add_vertex!(g)
add_vertices!(g, 2)
@test nv(g) == 3
@test ne(g) == 0

add_edge!(g, 1, 2)
add_edge!(g, 2, 3)
@test ne(g) == 2
@test ne(g, 1, 2) == 1
@test has_edge(g, 1, 2)
@test !has_edge(g, 1, 3)
@test outneighbors(g, 2) == [3]
@test inneighbors(g, 2) == [1]
@test all_neighbors(g, 2) == [1,3]

add_edge!(g, 1, 2)
@test ne(g) == 3
@test ne(g, 1, 2) == 2
@test outneighbors(g, 1) == [2,2]
@test inneighbors(g, 1) == []

end
