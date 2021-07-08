module TestCPortGraphs
using Test

using Catlab.Graphs, Catlab.WiringDiagrams, Catlab.CategoricalAlgebra
import Catlab.CategoricalAlgebra: migrate!

g = cycle_graph(Graph, 4)
pg = CPortGraph()
migrate!(pg, g)

@test subpart(pg, :box) == 1:4
@test subpart(pg, :src) == 1:4
@test subpart(pg, :tgt) == [2,3,4,1]

bar = Graph()
add_vertices!(bar, 2)
add_edge!(bar, 1,2)
Bar = migrate!(OpenCPortGraph(), bar)
@test subpart(Bar, :box) == 1:2
@test subpart(Bar, :con) == 1:2

opg = OpenCPortGraph(pg)
add_parts!(opg, :OuterPort, 2; con=[1,2])

g = OpenCPortGraph()
add_parts!(g, :Box, 2)
add_parts!(g, :Port, 4; box=[1,1,2,2])
add_parts!(g, :Wire, 2; src=[1,2], tgt=[3,4])
@test subpart(g, :src) == 1:2
@test subpart(g, :tgt) == 3:4
@test subpart(g, :box) == [1,1,2,2]
@test subpart(g, :con) == Int64[]

h = ocompose(g, [Bar, Bar])
@test subpart(h, :src) == [1,3,1,2]
@test subpart(h, :tgt) == [2,4,3,4]

barbell(k::Int) = begin
  g = OpenCPortGraph()
  add_parts!(g, :Box, 2)
  add_parts!(g, :Port, 2k; box=[fill(1,k); fill(2,k)])
  add_parts!(g, :Wire, k; src=1:k, tgt=k+1:2k)
  return g
end

@testset "Hexagon" begin
  g = OpenCPortGraph()
  add_parts!(g, :Box, 3)
  add_parts!(g, :Port, 6; box=[1,1,2,2,3,3])
  add_parts!(g, :Wire, 3; src=[2,4,6], tgt=[3,5,1])
  hex = ocompose(g, [Bar, Bar, Bar])
  @test subpart(hex, :src) == [1,3,5,2,4,6]
  @test subpart(hex, :tgt) == [2,4,6,3,5,1]
  @test subpart(hex, :con) == Int[]
  add_parts!(hex, :OuterPort, 6, con=1:6)

  twohex = ocompose(barbell(6), [hex, hex])
  g′ = migrate!(Graph(), migrate!(CPortGraph(), twohex))
  @test subpart(g′, :src) == [1,3,5,2,4,6,7,9,11,8,10,12,1,2,3,4,5,6]
  @test subpart(g′, :tgt) == [2,4,6,3,5,1,8,10,12,9,11,7,7,8,9,10,11,12]
end

@testset "Bundling CPGs" begin
  
  EdgeGraph() = begin
    g = Graph()
    add_parts!(g, :V, 2)
    add_parts!(g, :E, 1, src=[1], tgt=[2])
    return g
  end
  
  e₁ = EdgeGraph()
  oe₁ = migrate!(OpenCPortGraph(), (migrate!(CPortGraph(), e₁)))
  @test subpart(oe₁, :con) == 1:2
  mboe₁ = migrate!(BundledCPG(), oe₁)
  @test subpart(mboe₁, :bun) == 1:2
  
  boe₁ = BundledCPG(oe₁)
  add_parts!(boe₁, :Bundle, 1)
  set_subpart!(boe₁, :bun, [1,1])
  boe₁
  
  f = OpenCPortGraph(migrate!(CPortGraph(), e₁))
  f = BundledCPG(f)
  fee = ocompose(f, [boe₁, boe₁])
  @test fee[:, :src] == [1,3,1,2]
  @test fee[:, :tgt] == [2,4,3,4]
  
  add_parts!(f, :Bundle, 2)
  add_parts!(f, :OuterPort, 2, con=[1,2], bun=[1,2])
  fee′ = ocompose(f, [boe₁, boe₁])
  @test fee′[:, :con] == 1:4
  @test fee′[:, :bun] == [1,1,2,2]
  h = ocompose(f, [fee′, fee′])
  @test nparts(h, :Wire) == 10
  
  set_subpart!(fee′, :bun, 1)
  h = ocompose(f, [fee′, fee′])
  @test nparts(h, :Wire) == 12
end

end
