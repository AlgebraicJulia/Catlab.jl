module TestACSetMCO 

using Catlab, Test

# Partial overlaps with attributes 
#---------------------------------

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

# Maximum Common C-Set
######################
const WG = WeightedGraph{Bool}
"""
Searching for overlaps: •→•→•↺  vs ↻•→•→•
Two results: •→•→• || •↺ •→• 
"""
g1 = @acset WG begin 
  V=3; E=3; src=[1,1,2]; tgt=[1,2,3]; weight=[true,false,false]
end
g2 = @acset WG begin 
  V=3; E=3; src=[1,2,3]; tgt=[2,3,3]; weight=[true,false,false] 
end
apex1 = @acset WG begin
  V=3; E=2; Weight=2; src=[1,2]; tgt=[2,3]; weight=AttrVar.(1:2)
end
apex2 = @acset WG begin 
  V=3; E=2; Weight=2; src=[1,3]; tgt=[2,3]; weight=AttrVar.(1:2)
end

results = collect(maximum_common_subobject(g1, g2))
@test length(results) == 2
is_iso1 = map(result -> is_isomorphic(first(result), apex1), results)
@test sum(is_iso1) == 1
results = first(is_iso1) ? results : reverse(results)
(apx1,((L1,R1),)), (apx2,((L2,R2),)) = results
@test collect(L1[:V]) == [1,2,3]
@test collect(R1[:V]) == [1,2,3]
@test L1(apx1) == Subobject(g1, V=[1,2,3], E=[2,3])

@test is_isomorphic(apx2, apex2)
@test collect(L2[:V]) == [1,2,3]
@test collect(R2[:V]) == [3,1,2]
@test L2(apx2) == Subobject(g1, V=[1,2,3], E=[1,3])

# If we demand equality on attributes, max overlap is one false edge and all vertices.
exp = @acset WG begin V=3; E=1; src=1; tgt=2; weight=[false] end
@test first(first(maximum_common_subobject(g1, g2; abstract=false))) == exp


end # module