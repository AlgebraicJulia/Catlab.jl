module TestVarLimits 

using Test, Catlab

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,
                           index=[:src,:tgt]) <: AbstractGraph

# Terminal in the subcategory where all attrs are variables
T2 = ob(terminal(VELabeledGraph{Symbol}; cset=true))
@test T2 == @acset VELabeledGraph{Symbol} begin 
  V=1; E=1; Label=2; src=1; tgt=1; vlabel=[AttrVar(1)]; elabel=[AttrVar(2)]
end

end # module
