module TestCSetYoneda 

using Catlab, Test

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
