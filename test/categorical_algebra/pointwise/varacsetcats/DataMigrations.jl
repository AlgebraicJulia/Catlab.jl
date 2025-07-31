module TestVarDataMigrations 

using Catlab, Test

V, E, src, tgt = generators(SchGraph)
𝒞Grph =  FinCat(SchGraph)
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

F = FinFunctor(Dict(V => V, E=> E), Dict(src=>src, tgt=>tgt), 
               𝒞Grph, FinCat(SchWG); homtype=:generator)
Σ = SigmaMigrationFunctor(F, Graph, WG{Float64})

Grph = ACSetCategory(Graph())
G = @withmodel TypedCatWithCoproducts(Grph) (⊕) begin 
   path_graph(Graph,3) ⊕ Graph(1) # two connected components
end
expected = @acset WG{Float64} begin 
  V=4; E=2; Color=2; src=[2,3]; tgt=[3,1]; color=AttrVar.([1,1,1,2]) 
end

cat = ACSetCategory(VarACSetCat(expected))
@test is_isomorphic(Σ(G; cat), expected)
 
# Identity migration on weighted graphs.
Y = @acset WeightedGraph{Symbol} begin
  V=2; E=2; Weight=1; src=1; tgt=[1,2]; weight=[AttrVar(1), :X]
end
ΣF = SigmaMigrationFunctor(id[FinCatC()](FinCat(SchWeightedGraph)),
                           WeightedGraph{Symbol}, WeightedGraph{Symbol})
@test is_isomorphic(ΣF(Y; cat),Y)


# Two things example
####################

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
  Th1 = 2; Th2 = 4; f = [1,3]
  prop = [false,false,true,true]
  id = ["ffee cup","doughnut"]
end

Y = @acset Thing1WithProp{Bool,String} begin
  Th1 = 2; Th2 = 4; f = [1,3]
  prop = [false,true]
  id = ["ffee cup","doughnut"]
end

C1,C2 = FinCat(SchThing1WithProp), FinCat(SchThing2WithProp)

th1, th2, property, ID = ob_generators(C1)
f1, id1, prop1 = hom_generators(C1)
f2, id2, prop2 = hom_generators(C2)

F = FinFunctor(
  Dict(th1 => th1, th2 => th2, property => property,ID=>ID),
  Dict(f1 => [f2], prop1 => [f2, prop2],id1=>[id2]),
  C1, C2; homtype=:list
)

ΔF = DataMigrationFunctor(F, Thing2WithProp{Bool,String}, Thing1WithProp{Bool,String})
@test ΔF(X) == Y

ΣF = SigmaMigrationFunctor(F, Thing1WithProp{Bool,String}, Thing2WithProp{Bool,String})

cat = ACSetCategory(VarACSetCat(X))
XX = ΣF(Y; cat)
@test incident(XX,false,[:f,:prop]) == incident(XX,"ffee cup",:id)

end # module
