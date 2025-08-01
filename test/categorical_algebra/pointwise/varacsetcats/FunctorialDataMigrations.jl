module TestFunctorialDataMigrations
using Test

using Catlab.BasicSets, Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra

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
  Th1 = 2
  Th2 = 4
  f = [1,3]
  prop = [false,false,true,true]
  id = ["ffee cup","doughnut"]
end

Y = @acset Thing1WithProp{Bool,String} begin
  Th1 = 2
  Th2 = 4
  f = [1,3]
  prop = [false,true]
  id = ["ffee cup","doughnut"]
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
XX = ΣF(Y)
@test YY == Y
@test incident(XX,false,[:f,:prop]) == incident(XX,"ffee cup",:id)

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
