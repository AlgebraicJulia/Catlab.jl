module TestCSetDataMigrations

using Test, Catlab

@present SchDDS(FreeSchema) begin
  X::Ob; Φ::Hom(X,X)
end
@acset_type DDS(SchDDS, index=[:Φ])

h = Graph(3)
add_parts!(h, :E, 3, src = [1,2,3], tgt = [2,3,1])

# Identity data migration.
@test h == migrate(Graph, h, Dict(:V => :V, :E => :E),
                   Dict(:src => :src, :tgt => :tgt))

# Migrate DDS → Graph.
dds = DDS()
add_parts!(dds, :X, 3, Φ=[2,3,1])
X = SchDDS[:X]
FOb = Dict(:V => :X, :E => :X)
FHom = Dict(:src => id(X), :tgt => :Φ)
F = DeltaMigration(FinFunctor(FOb,FHom,SchGraph,SchDDS))
Δ(x) = migrate(Graph, x, FOb,FHom)

@test h == Δ(dds)

# test on morphisms
dds′ = @acset DDS begin X=5; Φ=[2,3,4,4,3] end
dds2 = @acset DDS begin X=3; Φ=[2,3,3] end 
f = ACSetTransformation(dds′,dds2; X=[1,2,3,3,3])
Δf = homomorphism(Δ(dds′),Δ(dds2); initial=(V=[1,2,3,3,3],))
@test Δf == migrate(Graph, f, F)

# Mutating migration
h2 = copy(h)
migrate!(h2, dds, FOb, FHom)
@test h2 == ob(coproduct(h, h))

# Migrate DDS → DDS by advancing four steps.
@test dds == migrate(DDS, dds, Dict(:X => :X),
                     Dict(:Φ => [:Φ, :Φ, :Φ, :Φ]))


#

# Sigma migration
#################

V1B, V2B, EB = generators(SchUndirectedBipartiteGraph, :Ob)
srcB, tgtB = generators(SchUndirectedBipartiteGraph, :Hom)

VG, EG = generators(SchGraph, :Ob)
srcG, tgtG = generators(SchGraph, :Hom)

F = FinFunctor(
  Dict(V1B => VG, V2B => VG, EB => EG),
  Dict(srcB => srcG, tgtB => tgtG),
  SchUndirectedBipartiteGraph, SchGraph
)
idF = id(FinCat(SchGraph))

ΣF = SigmaMigrationFunctor(F, UndirectedBipartiteGraph, Graph)
X = UndirectedBipartiteGraph()

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

Yd = ΣF(X; return_unit=true)
Y = Graph(codom(Yd))
α = diagram_map(Yd)
@test nparts(Y, :V) == 7
@test nparts(Y, :E) == 4
@test length(Y[:src] ∩ Y[:tgt]) == 0
@test isempty(collect(α[:V₁]) ∩ collect(α[:V₂]))

@test SigmaMigrationFunctor(idF, Graph, Graph)(Y) == Y


# Terminal map
#-------------
@present ThSpan(FreeSchema) begin
  (L1, L2, A)::Ob
  l1::Hom(A, L1)
  l2::Hom(A, L2)
end
@acset_type Span(ThSpan, index=[:l1, :l2])

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
@acset_type Initial(ThInitial)

L1, L2, A = generators(ThSpan, :Ob)
l1, l2 = generators(ThSpan, :Hom)
I = generators(ThInitial)[1]

bang = FinFunctor(
  Dict(L1 => I, L2 => I, A => I),
  Dict(l1 => id(I), l2 => id(I)),
  ThSpan, ThInitial
)

Σbang = SigmaMigrationFunctor(bang, Span, Initial)
Yd = Σbang(X; return_unit=true)
α = diagram_map(Yd)
@test length(unique([α[:A](1:2)...,α[:L1](1),α[:L2](1:2)...])) == 1
Y = Initial(codom(Yd))
@test nparts(Y, :I) == 4

# Map from terminal C 
#--------------------

V = FinFunctor(Dict(I => VG), Dict(), ThInitial, SchGraph)
E = FinFunctor(Dict(I => EG), Dict(), ThInitial, SchGraph)

Z = SigmaMigrationFunctor(V, Initial, Graph)(Y)
@test nparts(Z, :V) == 4
@test nparts(Z, :E) == 0

Z = SigmaMigrationFunctor(E, Initial, Graph)(Y)
expected = foldl(⊕,fill(path_graph(Graph,2), 4))  
@test is_isomorphic(Z,expected)

# Using the equations of the schema 
#----------------------------------
F = FinFunctor(
  Dict(:V => :V, :E=> :E),
  Dict(:src=>:src, :tgt=>:tgt),
  SchGraph, SchReflexiveGraph
)
G = path_graph(Graph,3)
Σ = SigmaMigrationFunctor(F, Graph, ReflexiveGraph)
expected = @acset ReflexiveGraph  begin 
  V=3; E=5; refl=1:3; src=[1,2,3,1,2]; tgt=[1,2,3,2,3] 
end 
@test is_isomorphic(Σ(G), expected)

end # module
