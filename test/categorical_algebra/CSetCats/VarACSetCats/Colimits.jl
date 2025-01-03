module TestVarACSetColimits 

using Test, Catlab

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,index=[:src,:tgt]) <: AbstractGraph

const VES = VELabeledGraph{Symbol}

const 𝒱 = ACSetCategory(VarACSetCat(VES()))

# Coproduct
###########

g = @acset VES begin V=2; E=2; Label=2; src=1; tgt=2; vlabel=[AttrVar(1),:b]; elabel=[:e, AttrVar(2)] end

expected = @acset VES begin 
  V=4; E=4; Label=4; src=[1,1,3,3]; tgt=[2,2,4,4]
  vlabel=[AttrVar(1),:b,AttrVar(3),:b]; 
  elabel=[:e,AttrVar(2),:e,AttrVar(4)] 
end

colim = ι₁, ι₂ = coproduct[𝒱](g,g)

@test ob(colim) == expected
@test ι₁[:V](1) == 1
@test ι₂[:V](1) == 3
@test ι₁[:Label](1) == 1
@test ι₂[:Label](1) == 3
@test ι₁[:Label](AttrVal(:x)) == AttrVal(:x)

end # module
