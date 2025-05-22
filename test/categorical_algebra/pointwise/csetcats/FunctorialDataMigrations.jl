module TestCSetFunctorialDataMigrations

using Test, Catlab

@present SchDDS(FreeSchema) begin X::Ob; Φ::Hom(X,X) end

@acset_type DDS(SchDDS, index=[:Φ])

###########################
# Contravariant migration #
###########################
V, E, src, tgt = generators(SchGraph)
Xdds, Φ = generators(SchDDS)

# Pullback migration
#-------------------

h = @acset Graph begin V=3; E=3; src = [1,2,3]; tgt = [2,3,1] end

# Identity data migration.
@test h == migrate(Graph, h, Dict(V => V, E => E),
                   Dict(src => src, tgt => tgt))

# Migrate DDS → Graph.
𝒞Grph, 𝒞DDS =  FinCat(SchGraph),FinCat(SchDDS)
dds = DDS()
add_parts!(dds, :X, 3, Φ=[2,3,1])
X = SchDDS[:X]
FOb = Dict(V => Xdds , E => Xdds)
FHom = Dict(src => Path(𝒞DDS, [],Xdds,Xdds), tgt => Path(𝒞DDS,[Φ]))

F = DeltaMigration(FinFunctor(FOb,FHom,𝒞Grph,𝒞DDS; homtype=:path))
Δ(x) = migrate(Graph, x, FOb,FHom; homtype=:path)

@test h == Δ(dds)

# test on morphisms
dds′ = @acset DDS begin X=5; Φ=[2,3,4,4,3] end
dds2 = @acset DDS begin X=3; Φ=[2,3,3] end 
f = ACSetTransformation(dds′,dds2; X=[1,2,3,3,3])
Δf = homomorphism(Δ(dds′),Δ(dds2); initial=(V=[1,2,3,3,3],))
@test Δf == migrate(Graph, f, F)

# Mutating migration
const 𝒞 = ACSetCategory(CSetCat(Graph()))

h2 = copy(h)
migrate!(h2, dds, FOb, FHom; homtype=:path)
@test h2 == ob(coproduct[𝒞](h, h))

# Migrate DDS → DDS by advancing four steps.
@test dds == migrate(DDS, dds, Dict(Xdds => Xdds),
                     Dict(Φ => Path(𝒞DDS, [Φ, Φ, Φ, Φ])); homtype=:path)
# Using the equations of cyclic schema to prevent infinite loop
###############################################################
𝒞Grph, 𝒞Refl =  FinCat(SchGraph), FinCat(SchReflexiveGraph)

V, E, src, tgt = generators(SchGraph)

F = FinFunctor(
  Dict(V => V, E=> E),
  Dict(src=>src, tgt=>tgt),
  𝒞Grph, 𝒞Refl; homtype=:generator
)

G = path_graph(Graph,3)

Σ = SigmaMigrationFunctor(F, Graph, ReflexiveGraph)

expected = @acset ReflexiveGraph  begin 
  V=3; E=5; refl=1:3; src=[1,2,3,1,2]; tgt=[1,2,3,2,3] 
end 

@test is_isomorphic(Σ(G), expected)

#########
# Sigma #
#########

V1B, V2B, EB, srcB, tgtB = generators(SchUndirectedBipartiteGraph)

VG, EG = generators(SchGraph, :Ob)
srcG, tgtG = generators(SchGraph, :Hom)

const 𝒢  = FinCat(SchGraph)
const ℬ  = FinCat(SchUndirectedBipartiteGraph)

F = FinFunctor(
  Dict(V1B => VG, V2B => VG, EB => EG),
  Dict(srcB => srcG, tgtB => tgtG),
  ℬ, 𝒢; homtype=:generator
)
idF = id[FinCatC()](FinCat(SchGraph))
ΣF = SigmaMigrationFunctor(F, UndirectedBipartiteGraph, Graph)
X = UndirectedBipartiteGraph()

Y = ΣF(X)
@test nparts(Y, :V) == 0
@test nparts(Y, :E) == 0

X = @acset UndirectedBipartiteGraph begin
  V₁ = 4; V₂ = 3; E = 4
  src = [1,2,2,3]; tgt = [1,1,2,3]
end

Yd = ΣF(X; return_unit=true);
F = codom[DiagramIdCat()](Yd)
Y = Graph(diagram(codom[DiagramIdCat()](Yd)))
α = diagram_map(Yd)
@test nparts(Y, :V) == 7
@test nparts(Y, :E) == 4
@test length(Y[:src] ∩ Y[:tgt]) == 0
v1b, v2b = collect.(getindex.([α,α], [V1B, V2B]))
@test isempty(v1b ∩ v2b)

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
  L1 = 3; L2 = 4; A = 3
  l1 = [1,1,2]; l2 = [1,2,3]
end

@present ThInitial(FreeSchema) begin
  I::Ob
end
@acset_type Initial(ThInitial)
const 𝒞I = FinCat(ThInitial)

L1, L2, A = generators(ThSpan, :Ob)
l1, l2 = generators(ThSpan, :Hom)
I = generators(ThInitial)[1]

bang = FinFunctor(
  Dict(L1 => I, L2 => I, A => I),
  Dict(l1 => id(I), l2 => id(I)),
  FinCat(ThSpan), 𝒞I; homtype=:hom
)

Σbang = SigmaMigrationFunctor(bang, Span, Initial)
Yd = Σbang(X; return_unit=true)
α = diagram_map(Yd)
a, l1, l2 = getindex.(Ref(α), [A,L1,L2])
@test length(unique([a.(1:2)...,l1(1),l2.(1:2)...])) == 1
Y = Initial(diagram(codom[DiagramIdCat()](Yd)))
@test nparts(Y, :I) == 4

# Map from terminal C
#--------------------

V = FinFunctor(Dict(I => VG), Dict(), 𝒞I, 𝒞Grph)
E = FinFunctor(Dict(I => EG), Dict(), 𝒞I, 𝒞Grph)

Z = SigmaMigrationFunctor(V, Initial, Graph)(Y)
@test nparts(Z, :V) == 4
@test nparts(Z, :E) == 0

Z = SigmaMigrationFunctor(E, Initial, Graph)(Y)

CM = TypedCatWithCoproducts(ACSetCategory(Graph()))
expected = @withmodel CM (⊕) begin 
  foldl(⊕,fill(path_graph(Graph,2), 4)) 
end 

@test is_isomorphic(Z,expected)

end # module
