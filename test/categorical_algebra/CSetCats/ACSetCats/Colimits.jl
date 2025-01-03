module TestACSetCatColimits 

using Catlab, Test 

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,index=[:src,:tgt]) <: AbstractGraph

const VES = VELabeledGraph{Symbol}
const 𝒟 = ACSetCategory(ACSetCat(VES()))

# Initial
#########

@test ob(initial[𝒟]()) == VES()

g = @acset VES begin V=2; E=1; src=1; tgt=2; vlabel=[:a,:b]; elabel=[:e] end

@test create[𝒟](g) == ACSetTransformation(VES(), g; cat=𝒟)

expected = @acset VES begin 
  V=4; E=2; src=[1,3]; tgt=[2,4]; vlabel=[:a,:b,:a,:b]; elabel=[:e,:e] 
end

@test expected == ob(coproduct[𝒟](g,g)) # replace with is_isomorphic once that's working

end # module
