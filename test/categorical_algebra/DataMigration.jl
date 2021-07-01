module TestDataMigration
using Test

using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphs.BasicGraphs: TheoryGraph, TheoryWeightedGraph
using Catlab.Graphs.BipartiteGraphs: TheoryUndirectedBipartiteGraph
using Catlab.Theories: id, compose
using Catlab.Present

# Pullback data migration
###########################

@present TheoryDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end

const AbstractDDS = AbstractCSetType(TheoryDDS)
const DDS = CSetType(TheoryDDS, index=[:Φ])

h = Graph(3)
add_parts!(h, :E, 3, src = [1,2,3], tgt = [2,3,1])

# Identity data migration.
@test h == Graph(h, Dict(:V => :V, :E => :E),
                    Dict(:src => :src, :tgt => :tgt))

# Migrate DDS → Graph.
dds = DDS()
add_parts!(dds, :X, 3, Φ=[2,3,1])
X = TheoryDDS[:X]
@test h == Graph(dds, Dict(:V => :X, :E => :X),
                 Dict(:src => id(X), :tgt => :Φ))

h2 = copy(h)
migrate!(h2, dds, Dict(:V => :X, :E => :X),
                  Dict(:src => id(X), :tgt => :Φ))
@test h2 == ob(coproduct(h, h))

# Migrate DDS → DDS by advancing four steps.
@test dds == DDS(dds, Dict(:X => :X),
                      Dict(:Φ => [:Φ, :Φ, :Φ, :Φ]))

@present TheoryLabeledDDS <: TheoryDDS begin
  Label::Data
  label::Attr(X, Label)
end
const LabeledDDS = ACSetType(TheoryLabeledDDS, index=[:Φ, :label])

S, ϕ, Label, label = generators(TheoryLabeledDDS)
V, E, s, t, Weight, weight = generators(TheoryWeightedGraph)

ldds = LabeledDDS{Int}()
add_parts!(ldds, :X, 4, Φ=[2,3,4,1], label=[100, 101, 102, 103])

wg = WeightedGraph{Int}(4)
add_parts!(wg, :E, 4, src=[1,2,3,4], tgt=[2,3,4,1], weight=[101, 102, 103, 100])

@test wg == WeightedGraph{Int}(ldds,
  Dict(:V => :X, :E => :X),
  Dict(:src => id(S), :tgt => :Φ, :weight => [:Φ, :label]))

@test Presentation(Graph(1)) == TheoryGraph
@test Presentation(ldds) == TheoryLabeledDDS


F = Functor(
  Dict(V => S, E => S), 
  Dict(s => id(S), t => ϕ, weight => compose(ϕ, label)),
  TheoryWeightedGraph, TheoryLabeledDDS
)

ΔF = Delta(F)
@test dom(ΔF) == ACSetType(TheoryLabeledDDS)
@test codom(ΔF) == ACSetType(TheoryWeightedGraph)

@test wg == WeightedGraph{Int}(ldds, F) 


# Left Pushforward data migration
#################################

Σ = Sigma

V1B, V2B, EB = generators(TheoryUndirectedBipartiteGraph, :Ob)
srcB, tgtB = generators(TheoryUndirectedBipartiteGraph, :Hom)

VG, EG = generators(TheoryGraph, :Ob)
srcG, tgtG = generators(TheoryGraph, :Hom)

F = Functor(
    Dict(V1B => VG, V2B => VG, EB => EG), 
    Dict(srcB => srcG, tgtB => tgtG),
    TheoryUndirectedBipartiteGraph, TheoryGraph
)

idF = Functor(
  Dict(VG => VG, EG => EG),
  Dict(srcG => srcG, tgtG => tgtG),
  TheoryGraph, TheoryGraph
)

ΣF =  Σ(F)
@test dom(ΣF) == ACSetType(TheoryUndirectedBipartiteGraph)
@test codom(ΣF) == ACSetType(TheoryGraph)

X = ACSetType(TheoryUndirectedBipartiteGraph, index=[:src, :tgt])()
Y = ΣF(X)

@test nparts(Y, :V) == 0
@test nparts(Y, :E) == 0

X = @acset UndirectedBipartiteGraph begin
  V₁ = 4
  V₂ = 3
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
const Span = ACSetType(ThSpan, index=[:l1, :l2])

X = @acset Span begin
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

end #module