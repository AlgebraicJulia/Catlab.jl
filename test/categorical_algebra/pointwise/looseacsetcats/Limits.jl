module TestLooseACSetLimits 

using Catlab, Test

# Simplest schema with attribute 
################################

@present SchSetAttr(FreeSchema) begin
  X::Ob; D::AttrType; f::Attr(X,D)
end
@acset_type SetAttr(SchSetAttr)
const Sym = SetAttr{Symbol}
cat = ACSetCategory(LooseACSetCat(Sym()))
term = @acset SetAttr{Tuple{}} begin X=1; f=[()] end

@test ob(terminal[cat]()) == term


A =  @acset Sym begin X=1; f=[:A] end
B =  @acset Sym begin X=1; f=[:B] end 

dA = delete[cat](A)
@test () == dA[:D](:x)

p1, p2 = product[cat](A,B)
@test p1[:D]((:A,:B)) == :A
@test only(dom(p1)[:f]) == (:A,:B)

BC =  @acset Sym begin X=2; f=[:B,:C] end 
dBC = delete[cat](BC)
l = pullback[cat](dA,dBC)
@test ob(l)[:f] == [(:A,:B),(:A,:C)]

##########
# Graphs #
##########

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,
                           index=[:src,:tgt]) <: AbstractGraph

const VEG = VELabeledGraph{Symbol}
const 𝒞 = ACSetCategory(LooseACSetCat(VEG()))


# Terminal labeled graph (across all possible choices of Julia data types)
o = ob(terminal[𝒞]())

@test (ob(terminal[𝒞]()) ==
  cycle_graph(VELabeledGraph{Tuple{}}, 1; E=(;elabel=[()]), V=(;vlabel=[()])))

# Product of labeled graphs.
g = path_graph(VELabeledGraph{Symbol}, 2, V=(vlabel=[:a,:b],), E=(elabel=:f,))
h = path_graph(VELabeledGraph{String}, 2, V=(vlabel=["x","y"],), E=(elabel="f",))
π1, π2 = lim = product[𝒞](g, h)
prod′ = ob(lim)
@test prod′ isa VELabeledGraph{Tuple{Symbol,String}}
@test Set(prod′[:vlabel]) == Set([(:a, "x"), (:a, "y"), (:b, "x"), (:b, "y")])
@test only(prod′[:elabel]) == (:f, "f")
@test prod′[src(prod′,1), :vlabel] == (:a, "x")
@test prod′[tgt(prod′,1), :vlabel] == (:b, "y")
@test is_natural(π1) && is_natural(π2)
@test components(π1)[:Label]((:a, "x")) == :a
@test components(π2)[:Label]((:a, "x")) == "x"


# Limit with ACSetTransformations 
# NO LONGER SUPPORTED
# A = @acset VELabeledGraph{Symbol} begin V=2; vlabel=[:a,:b] end;
# B = @acset VELabeledGraph{Symbol} begin V=2; vlabel=[:q,:z] end;
# C = @acset VELabeledGraph{Symbol} begin V=2; vlabel=[:x,:y] end;
# ac = ACSetTransformation(
#   Dict([:V=>[1,2], :Label=>FinFunction(Dict(:a=>:x,:b=>:y))]),A,C; cat=𝒞);
# bc = ACSetTransformation(
#   Dict([:V=>[1,1], :Label=>FinFunction(Dict(:q=>:x,:z=>:x))]),B,C; cat=𝒞);
# @test all(is_natural,[ac,bc])
# res = limit[𝒞](Cospan(ac,bc));
# @test all(is_natural,legs(res))
# @test apex(res)[:vlabel] == [(:a,:q),(:a,:z)]


# WeightedGraphs 
#################

const WG = WeightedGraph
const 𝒟 = ACSetCategory(LooseACSetCat(WG{Int}()))

# Pullback of weighted graphs.
g0 = WeightedGraph{Nothing}(2)
add_edges!(g0, 1:2, 1:2)
g = WeightedGraph{Int}(4)
add_edges!(g, [1,3], [2,4], weight=[+1, -1])
ϕ = ACSetTransformation((V=[1,1,2,2], E=[1,2]), g, g0; cat=𝒟)
ψ = ACSetTransformation((V=[2,2,1,1], E=[2,1]), g, g0; cat=𝒟)
pb = ob(pullback[𝒟](ϕ, ψ))
@test (nv(pb), ne(pb)) == (8, 2)
@test Set(pb[:weight]) == Set([(+1, -1), (-1, +1)])

end # module
