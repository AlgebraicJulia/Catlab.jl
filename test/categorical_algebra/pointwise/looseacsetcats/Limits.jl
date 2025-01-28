module TestLooseACSetLimits 

using Catlab, Test

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,
                           index=[:src,:tgt]) <: AbstractGraph

# Terminal labeled graph (across all possible choices of Julia data types)
@test ob(terminal(VELabeledGraph; loose=true)) == 
  cycle_graph(VELabeledGraph{Tuple{}}, 1; E=(;elabel=[()]), V=(;vlabel=[()]))

# Terminal in the subcategory where all attrs are variables
T2 = ob(terminal(VELabeledGraph{Symbol}; cset=true))
@test T2 == @acset VELabeledGraph{Symbol} begin 
  V=1; E=1; Label=2; src=1; tgt=1; vlabel=[AttrVar(1)]; elabel=[AttrVar(2)]
end

# Product of labeled graphs.
g = path_graph(VELabeledGraph{Symbol}, 2, V=(vlabel=[:a,:b],), E=(elabel=:f,))
h = path_graph(VELabeledGraph{String}, 2, V=(vlabel=["x","y"],), E=(elabel="f",))
π1, π2 = lim = product(g, h; loose=true)
prod′ = ob(lim)
@test prod′ isa VELabeledGraph{Tuple{Symbol,String}}
@test Set(prod′[:vlabel]) == Set([(:a, "x"), (:a, "y"), (:b, "x"), (:b, "y")])
@test only(prod′[:elabel]) == (:f, "f")
@test prod′[src(prod′,1), :vlabel] == (:a, "x")
@test prod′[tgt(prod′,1), :vlabel] == (:b, "y")
@test is_natural(π1) && is_natural(π2)
@test type_components(π1)[:Label]((:a, "x")) == :a
@test type_components(π2)[:Label]((:a, "x")) == "x"

# Pullback of weighted graphs.
g0 = WeightedGraph{Nothing}(2)
add_edges!(g0, 1:2, 1:2)
g = WeightedGraph{Int}(4)
add_edges!(g, [1,3], [2,4], weight=[+1, -1])
ϕ = LooseACSetTransformation((V=[1,1,2,2], E=[1,2]),(Weight=nothing,), g, g0)
ψ = LooseACSetTransformation((V=[2,2,1,1], E=[2,1]), (Weight=nothing,),g, g0)
pb = ob(pullback(ϕ, ψ))
@test (nv(pb), ne(pb)) == (8, 2)
@test Set(pb[:weight]) == Set([(+1, -1), (-1, +1)])

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
