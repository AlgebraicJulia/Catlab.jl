module TestFunctorialDataMigrations

using Test, Catlab

@present SchSet(FreeSchema) begin
  X::Ob
end
@acset_type AcsetSet(SchSet)

@present SchDDS <: SchSet begin
  Φ::Hom(X,X)
end
@acset_type DDS(SchDDS, index=[:Φ])

# Contravariant migration
#########################

# Pullback migration
#-------------------

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
Ff = FinFunctor(FOb,FHom,SchGraph,SchDDS)
F = DeltaMigration(Ff)
Δ(x) = migrate(Graph, x, FOb,FHom)

@test h == Δ(dds)

# test SimpleMigration on objects and morphisms
Delta = ΔMigration(Ff, Graph)
dds′ = @acset DDS begin X=5; Φ=[2,3,4,4,3] end
dds2 = @acset DDS begin X=3; Φ=[2,3,3] end 
f = ACSetTransformation(dds′,dds2; X=[1,2,3,3,3])
Δf = homomorphism(Delta(dds′),Delta(dds2); initial=(V=[1,2,3,3,3],))
@test Δf == migrate(Graph, f, F)
@test Delta(f) == Δf

# Mutating migration
h2 = copy(h)
migrate!(h2, dds, FOb, FHom)
@test h2 == ob(coproduct(h, h))

# Migrate DDS → DDS by advancing four steps.
@test dds == migrate(DDS, dds, Dict(:X => :X),
                     Dict(:Φ => [:Φ, :Φ, :Φ, :Φ]))

@present SchLabeledDDS <: SchDDS begin
  Label::AttrType
  label::Attr(X, Label)
end
@acset_type LabeledDDS(SchLabeledDDS, index=[:Φ, :label])

S, ϕ, Label, label = generators(SchLabeledDDS)
V, E, s, t, Weight, weight = generators(SchWeightedGraph)

ldds = LabeledDDS{Int}()
add_parts!(ldds, :X, 4, Φ=[2,3,4,1], label=[100, 101, 102, 103])

wg = WeightedGraph{Int}(4)
add_parts!(wg, :E, 4, src=[1,2,3,4], tgt=[2,3,4,1], weight=[101, 102, 103, 100])

@test wg == migrate(WeightedGraph{Int}, ldds,
  Dict(:V => :X, :E => :X, :Weight => :Label),
  Dict(:src => id(S), :tgt => :Φ, :weight => [:Φ, :label]))

@test Presentation(Graph(1)) == SchGraph
@test Presentation(ldds) == SchLabeledDDS

F = FinFunctor(
  Dict(V => S, E => S, Weight => Label),
  Dict(s => id(S), t => ϕ, weight => compose(ϕ, label)),
  SchWeightedGraph, SchLabeledDDS
)
ΔF = DataMigrationFunctor(F, LabeledDDS{Int}, WeightedGraph{Int})
@test wg == ΔF(ldds)

idF = id(FinCat(SchLabeledDDS))
@test ldds == migrate(LabeledDDS{Int}, ldds, DeltaMigration(idF))

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
  V₁ = 4; V₂ = 3; E = 4; src = [1,2,2,3]; tgt = [1,1,2,3]
end

Yd = ΣF(X; return_unit=true)
Y = Graph(codom(Yd))
α = diagram_map(Yd)
@test nparts(Y, :V) == 7
@test nparts(Y, :E) == 4
@test length(Y[:src] ∩ Y[:tgt]) == 0
@test isempty(collect(α[:V₁]) ∩ collect(α[:V₂]))

# SimpleMigration Sigma acting on objects and morphisms
Sigma = ΣMigration(F, Graph)
Y = Sigma(X)
X′ = @acset UndirectedBipartiteGraph begin
  V₁ = 4; V₂ = 3; E = 4; src = [1,2,2,3]; tgt = [1,1,2,1]
end
f = homomorphism(X, X′; initial=(V₁=1:4,E=1:4))
@test is_natural(Sigma(f))

# Id action
@test SigmaMigrationFunctor(idF, Graph, Graph)(Y) == Y


# With AttrVars
@present SchAttrSet(FreeSchema) begin X::Ob; D::AttrType; (f)::Attr(X,D) end
@acset_type AttrSet(SchAttrSet){Symbol}

F = id(FinCat(SchAttrSet))
s = ΣMigration(F, AttrSet)
X = @acset AttrSet begin X=2; D=1; f=[:abc, AttrVar(1)] end
s(X; return_unit=true)

# Sheep example (abstracted to MWE)
@present SchQ(FreeSchema) begin (X)::Ob; D::AttrType; (f,g)::Attr(X, D) end
@acset_type Q(SchQ, part_type=BitSetParts){Symbol}
X = @acset Q begin X=1; D=1; f=[AttrVar(1)]; g=[AttrVar(1)]  end
r = ΣMigration(id(FinCat(SchQ)), Q)(id(X));

# Migrate wandering attrvars
X = @acset AttrSet begin X=1; D=3; f=[AttrVar(2)] end
@test is_isomorphic(X, s(X)) # not equal, though due to reordering of attrvars
ΣX = s(X;return_unit=true)
@test is_natural(ΣX.diagram_map)


# Sigma migrations with attributes
#---------------------------------

# Identity migration on weighted graphs.
Y = @acset WeightedGraph{Symbol} begin
  V=2; E=2; Weight=1; src=1; tgt=[1,2]; weight=[AttrVar(1), :X]
end
ΣF = SigmaMigrationFunctor(id(FinCat(SchWeightedGraph)),
                           WeightedGraph{Symbol}, WeightedGraph{Symbol})
@test is_isomorphic(ΣF(Y),Y)

# Less trivial example.
@present SchTwoThings(FreeSchema) begin
  Th1::Ob
  Th2::Ob
  Property::AttrType
  # The ID attribute keeps track of combinatorial objects as their
  # non-meaningful integer IDs may be modified by the chase.
  ID::AttrType
  f::Hom(Th1,Th2)
  id::Attr(Th1,ID)
end
@present SchThing1WithProp <: SchTwoThings begin
  prop::Attr(Th1,Property)
end
@acset_type Thing1WithProp(SchThing1WithProp)
@present SchThing2WithProp <: SchTwoThings begin
  prop::Attr(Th2,Property)
end
@acset_type Thing2WithProp(SchThing2WithProp)

X = @acset Thing2WithProp{Bool,String} begin
  Th1 = 2; Th2 = 4; f = [1,3]; prop = [false,false,true,true]; 
  id = ["ffee cup","doughnut"]
end

Y = @acset Thing1WithProp{Bool,String} begin
  Th1 = 2; Th2 = 4; f = [1,3]; prop = [false,true]; id = ["ffee cup","doughnut"]
end

C1,C2 = FinCat(SchThing1WithProp),FinCat(SchThing2WithProp)
th1,th2,property,ID = ob_generators(C1)
f1,id1,prop1 = hom_generators(C1)
f2,id2,prop2 = hom_generators(C2)

F = FinFunctor(
  Dict(th1 => th1, th2 => th2, property => property,ID=>ID),
  Dict(f1 => f2, prop1 => [f2, prop2],id1=>id2),
  SchThing1WithProp, SchThing2WithProp
)

ΔF = DataMigrationFunctor(F, Thing2WithProp{Bool,String}, Thing1WithProp{Bool,String})
ΣF = SigmaMigrationFunctor(F, Thing1WithProp{Bool,String}, Thing2WithProp{Bool,String})

YY = ΔF(X)
XX = ΣF(Y);
@test YY == Y
@test incident(XX,false,[:f,:prop]) == incident(XX,"ffee cup",:id)

# Terminal map
#-------------
@present ThSpan(FreeSchema) begin
  (L1, L2, A)::Ob
  l1::Hom(A, L1)
  l2::Hom(A, L2)
end
@acset_type Span(ThSpan, index=[:l1, :l2])

X = @acset Span begin L1 = 3; L2 = 4; A = 3; l1 = [1,1,2]; l2 = [1,2,3] end

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

# Sigma with attributes 
#----------------------
#XX: Isn't this tested twice?
# Connected components must be monochromatic
@present SchWG <: SchGraph begin
  Color::AttrType
  color::Attr(V,Color)
  src ⋅ color == tgt ⋅ color
end
@acset_type WG(SchWG)

F = FinFunctor(Dict(:V => :V, :E=> :E), Dict(:src=>:src, :tgt=>:tgt), SchGraph, SchWG)
Σ = SigmaMigrationFunctor(F, Graph, WG{Float64})

G = path_graph(Graph,3) ⊕ Graph(1) # two connected components
expected = @acset WG{Float64} begin 
  V=4; E=2; Color=2; src=[2,3]; tgt=[3,1]; color=AttrVar.([1,1,1,2]) 
end

@test is_isomorphic(Σ(G), expected)

W = @acset WG{Float64} begin Color=1 end
Σ = ΣMigration(id(FinCat(SchWG)), WG{Float64})
Σ(W; return_unit=true)
ob_map(force(FinDomFunctor(W)), :Color)
 

# Reduced sheep example
@present SchZ(FreeSchema) begin D::AttrType; end
@acset_type Z2(SchZ, part_type=BitSetParts){Symbol}
ΣMigration(id(FinCat(SchZ)), Z2)(Z2(); return_unit=true)

# Yoneda embedding
#-----------------

# Yoneda embedding for graphs (no attributes).
yV, yE = Graph(1), @acset(Graph, begin V=2;E=1;src=2;tgt=1 end)
@test representable(Graph, :V) == yV
@test is_isomorphic(representable(Graph, :E), yE)

y_Graph = yoneda(Graph)
@test ob_map(y_Graph, :V) == yV
@test is_isomorphic(ob_map(y_Graph, :E), yE)
@test Set(hom_map.(Ref(y_Graph), [:src,:tgt])) == Set(
  homomorphisms(yV, representable(Graph, :E)))
y_Graph_Dynamic = yoneda(DynamicACSet(Graph()))
@test all([is_isomorphic(DynamicACSet(ob_map(y_Graph,x)),ob_map(y_Graph_Dynamic,x)) for x in [:V,:E]])

# Subobject classifier
######################
# Graph and ReflGraph have 'same' subobject classifier
ΩG,_ = subobject_classifier(Graph)
ΩrG,_ = subobject_classifier(ReflexiveGraph)
F = FinFunctor(Dict(:V=>:V, :E=>:E), Dict(:src=>:src, :tgt=>:tgt), 
               SchGraph, SchReflexiveGraph)
ΔF = DataMigrationFunctor(F, ReflexiveGraph, Graph)
@test is_isomorphic(ΩG, ΔF(ΩrG))

# Searching for maps into the subobject classifier is much faster than 
# enumerating them via `subobject_graph`
G = (star_graph(Graph, 2)⊗path_graph(Graph, 3))
@test length(homomorphisms(G, ΩG)) == length(subobject_graph(G)[2])

@present SchDDS42(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
  Φ⋅Φ⋅Φ⋅Φ == Φ⋅Φ
end
@acset_type DDS42(SchDDS42, index=[:Φ])
ΩDDs, _ = subobject_classifier(DDS42)
@test is_isomorphic(ΩDDs, @acset DDS42 begin X=4; Φ=[1,3,4,4] end)

# Internal Hom
##############
G = ReflexiveGraph(2)
F = path_graph(ReflexiveGraph, 2)
Fᴳ,_ = internal_hom(G, F)
Z = apex(terminal(ReflexiveGraph)) ⊕ path_graph(ReflexiveGraph, 3)
@test length(homomorphisms(Z, Fᴳ)) == length(homomorphisms(Z ⊗ G, F)) # 64

G = @acset DDS42 begin X=3; Φ=[2,3,3] end
F = @acset DDS42 begin X=4; Φ=[2,2,4,4] end
Fᴳ,_ = internal_hom(G, F)
Z = @acset DDS42 begin X=5; Φ=[2,3,4,3,4] end
@test length(homomorphisms(Z, Fᴳ)) == length(homomorphisms(Z ⊗ G, F)) # 1024

end # module
