module TestDataMigration
using Test

using Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.Theories: id
using Catlab.Present

@present ThBipartite(FreeSchema) begin
  (V1, V2, E)::Ob
  src::Hom(E, V1)
  tgt::Hom(E, V2)
end

V1B, V2B, EB = generators(ThBipartite, :Ob)
srcB, tgtB = generators(ThBipartite, :Hom)

VG, EG = generators(TheoryGraph, :Ob)
srcG, tgtG = generators(TheoryGraph, :Hom)

F = Functor(
    Dict{FreeSchema.Ob, FreeSchema.Ob}(V1B => VG, V2B => VG, EB => EG), 
    Dict{FreeSchema.Hom, FreeSchema.Hom}(srcB => srcG, tgtB => tgtG),
    ThBipartite, TheoryGraph
)

idF = Functor(
  Dict{FreeSchema.Ob, FreeSchema.Ob}(VG => VG, EG => EG),
  Dict{FreeSchema.Hom, FreeSchema.Hom}(srcG => srcG, tgtG => tgtG),
  TheoryGraph, TheoryGraph
)

ΣF =  Σ(F)
X = ACSetType(ThBipartite, index=[:src, :tgt])()
Y = ΣF(X)

@test nparts(Y, :V) == 0
@test nparts(Y, :E) == 0

X =  @acset ACSetType(ThBipartite, index=[:src, :tgt]) begin
  V1 = 4
  V2 = 3
  E = 4
  src = [1,2,2,3]
  tgt = [1,1,2,3]
end

Y = ΣF(X)
@test nparts(Y, :V) == 7
@test nparts(Y, :E) == 4
@test length(Y[:src] ∩ Y[:tgt]) == 0

@test Σ(idF)(Y) == Y

@present ThSpan(FreeSchema) begin 
  (L1, L2, A)::Ob
  l1::Hom(A, L1)
  l2::Hom(A, L2)
end

X = @acset ACSetType(ThSpan, index=[:l1, :l2]) begin
  L1 = 3
  L2 = 4
  A = 3
  l1 = [1,1,2]
  l2 = [1,2,3]
end

@present ThInitial(FreeSchema) begin
  I::Ob
end

L1, L2, A = generators(ThSpan, :Ob)
l1, l2 = generators(ThSpan, :Hom)
I = generators(ThInitial)[1]

bang = Functor(
  Dict{FreeSchema.Ob, FreeSchema.Ob}(L1 => I, L2 => I, A => I),
  Dict{FreeSchema.Hom, FreeSchema.Hom}(l1 => id(I), l2 => id(I)),
  ThSpan, ThInitial
)

Y = Σ(bang)(X)

@test nparts(Y, :I) == 4

vertex = Functor(
  Dict{FreeSchema.Ob, FreeSchema.Ob}(I => VG),
  Dict{FreeSchema.Hom, FreeSchema.Hom}(),
  ThInitial, TheoryGraph
)
edge = Functor(
  Dict{FreeSchema.Ob, FreeSchema.Ob}(I => EG), 
  Dict{FreeSchema.Hom, FreeSchema.Hom}(),
  ThInitial, TheoryGraph
)

Z = Σ(vertex)(Y)
@test nparts(Z, :V) == 4
@test nparts(Z, :E) == 0

Z = Σ(edge)(Y)
@test nparts(Z, :V) == 8
@test nparts(Z, :E) == 4
@test Z[:src] ∪ Z[:tgt] == 1:8

end #module}