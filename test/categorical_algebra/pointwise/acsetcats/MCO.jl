module TestACSetMCO 

# Partial overlaps with attributes 

@present SchVELabeledGraph <: SchGraph begin
  VL::AttrType; EL::AttrType; vlabel::Attr(V,VL); elabel::Attr(E,EL)
end

@acset_type VELabeledGraph(SchVELabeledGraph) <: AbstractGraph
const LGraph = VELabeledGraph{Bool,Bool}

G = @acset LGraph begin 
  V=3; E=2; src=[1,2]; tgt=[2,3]; vlabel=Bool[0,1,1]; elabel=Bool[0,1]
end
H = @acset LGraph begin 
  V=3; E=2; src=[1,2]; tgt=[2,3]; vlabel=Bool[0,0,1]; elabel=Bool[0,0]
end
os = partial_overlaps(G, H); # abstract=true
@test count(apx->nparts(apx,:E)==2, apex.(os)) == 1
os = partial_overlaps(G, H; abstract=[:VL]);
@test count(apx->nparts(apx,:E)==2, apex.(os)) == 0
@test count(apx->nparts(apx,:E)==1, apex.(os)) == 4
os = partial_overlaps(G, H; abstract=false);
@test count(apx->nparts(apx,:E)==2, apex.(os)) == 0
@test count(apx->nparts(apx,:E)==1, apex.(os)) == 1

end # module
