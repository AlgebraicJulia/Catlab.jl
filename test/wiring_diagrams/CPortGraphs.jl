using Test
using Catlab
using Catlab.Graphs
using Catlab.WiringDiagrams
using Catlab.WiringDiagrams.CPortGraphs
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.CSets
import Catlab.CategoricalAlgebra.CSets: migrate!


g = Graph()
add_vertices!(g, 4)
add_edges!(g, [1,2,3,4], [2,3,4,1])

pg = CPortGraph()
migrate!(pg, g)

@test subpart(pg, :, :box) == 1:4
@test subpart(pg, :, :src) == 1:4
@test subpart(pg, :, :tgt) == [2,3,4,1]

bar = Graph()
add_vertices!(bar, 2)
add_edge!(bar, 1,2)
Bar = migrate!(OpenCPortGraph(), bar)
@test subpart(Bar, :, :box) == 1:2
@test subpart(Bar, :, :con) == 1:2

opg = OpenCPortGraph(pg)
add_parts!(opg, :OP, 2; con=[1,2])

g = OpenCPortGraph()
add_parts!(g, :B, 2)
add_parts!(g, :P, 4; box=[1,1,2,2])
add_parts!(g, :W, 2; src=[1,2], tgt=[3,4])
@test subpart(g, :, :src) == 1:2
@test subpart(g, :, :tgt) == 3:4
@test subpart(g, :, :box) == [1,1,2,2]
@test subpart(g, :, :con) == Int64[]

h = ocompose(g, [Bar, Bar])
@test subpart(h, :, :src) == [1,3,1,2]
@test subpart(h, :, :tgt) == [2,4,3,4]

barbell(k::Int) = begin
  g = OpenCPortGraph()
  add_parts!(g, :B, 2)
  add_parts!(g, :P, 2k; box=[fill(1,k); fill(2,k)])
  add_parts!(g, :W, k; src=1:k, tgt=k+1:2k)
  return g
end

@testset "Hexagon" begin
  g = OpenCPortGraph()
  add_parts!(g, :B, 3)
  add_parts!(g, :P, 6; box=[1,1,2,2,3,3])
  add_parts!(g, :W, 3; src=[2,4,6], tgt=[3,5,1])
  hex = ocompose(g, [Bar, Bar, Bar])
  @test subpart(hex, :, :src) == [1,3,5,2,4,6]
  @test subpart(hex, :, :tgt) == [2,4,6,3,5,1]
  @test subpart(hex, :, :con) == 1:6

  twohex = ocompose(barbell(6), [hex, hex])
  g′ = migrate!(Graph(), migrate!(CPortGraph(), twohex))
  @test subpart(g′, :, :src) == [1, 3, 5, 2, 4, 6, 7, 9, 11, 8, 10, 12, 1, 2, 3, 4, 5, 6]
  @test subpart(g′, :, :tgt) == [2, 4, 6, 3, 5, 1, 8, 10, 12, 9, 11, 7, 7, 8, 9, 10, 11, 12] 
end

