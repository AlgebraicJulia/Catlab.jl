module TestLooseACSetLimits
using Catlab, Test

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,
                           index=[:src,:tgt]) <: AbstractGraph

# Terminal labeled graph (across all possible choices of Julia data types)
@test ob(terminal(VELabeledGraph; loose=true)) == 
  cycle_graph(VELabeledGraph{Tuple{}}, 1; E=(;elabel=[()]), V=(;vlabel=[()]))

# Limit with LooseACSetTransformations 
A = @acset VELabeledGraph{Symbol} begin V=2; vlabel=[:a,:b] end;
B = @acset VELabeledGraph{Symbol} begin V=2; vlabel=[:q,:z] end;
C = @acset VELabeledGraph{Symbol} begin V=2; vlabel=[:x,:y] end;
ac = LooseACSetTransformation(
  Dict([:V=>[1,2]]),Dict([:Label=>FinFunction(Dict(:a=>:x,:b=>:y))]),A,C);
bc = LooseACSetTransformation(
  Dict([:V=>[1,1]]),Dict([:Label=>FinFunction(Dict(:q=>:x,:z=>:x))]),B,C);
@test all(is_natural,[ac,bc])
res = limit(Cospan(ac,bc); product_attrs=true);
@test all(is_natural,legs(res))
@test apex(res)[:vlabel] == [(:a,:q),(:a,:z)]

end # module
