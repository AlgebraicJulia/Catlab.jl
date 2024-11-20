module TestACSetSetInterop 

using ACSets, Catlab, Test

@present SchDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end
@acset_type DDS(SchDDS, index=[:Φ])

@present SchSetAttr(FreeSchema) begin
  X::Ob
  D::AttrType
  f::Attr(X,D)
end
@acset_type SetAttr(SchSetAttr)


g = Graph(6)
add_edges!(g, 2:4, 3:5)
@test FinSet(g, :V) == FinSet(6)
@test FinFunction(g, :V) == id[SetC()](FinSet(6))
f = FinFunction(g, :src)
@test codom(f) == FinSet(6)
@test collect(f) == 2:4

# IS THIS REALLY NEEDED?
# f = FinDomFunction(g, :E)
# @test collect(f) == 1:3
# # @test is_indexed(f)
# f = FinDomFunction(g, :tgt)
# @test codom(f) == SetOb(Int)
# @test collect(f) == 3:5

g = path_graph(WeightedGraph{Float64}, 3, E=(weight=[0.5, 1.5],))
@test TypeSet(g, :Weight) == TypeSet(Float64)
@test TypeSet(g, :V) == TypeSet(Int)
@test_throws ArgumentError TypeSet(g, :W)

f = FinDomFunction(g, :weight)
@test codom(f) == SetOb(Float64)
@test collect(f) == [0.5, 1.5]


end # module
