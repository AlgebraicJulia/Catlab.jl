module TestACSetLimits 

using Catlab, Test 

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph, index=[:src,:tgt]
                          ) <: AbstractGraph


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

end # module
