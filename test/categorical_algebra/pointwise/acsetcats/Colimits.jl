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


# Coproduct 
###########

# A coproduct of a graph with itself
colim = coproduct[𝒟](g, g)

expected = @acset VES begin 
  V=4; E=2; src=[1,3]; tgt=[2,4]; vlabel=[:a,:b,:a,:b]; elabel=[:e,:e] 
end

@test is_isomorphic(expected, ob(colim)) 

# Coproduct of different labeled graphs.
g = path_graph(VELabeledGraph{Symbol}, 2, V=(vlabel=[:u,:v],), E=(elabel=:e,))
h = cycle_graph(VELabeledGraph{Symbol}, 1, V=(vlabel=:u,), E=(elabel=:f,))
coprod = ob(coproduct[𝒟](g, h))
@test subpart(coprod, :vlabel) == [:u, :v, :u]
@test subpart(coprod, :elabel) == [:e, :f]

# Pushouts
##########

g0 = VELabeledGraph{Symbol}()
add_vertex!(g0, vlabel=:u)
α = ACSetTransformation((V=[1], E=Int[]), g0, g)
β = ACSetTransformation((V=[1], E=Int[]), g0, h)
@test is_natural(α) && is_natural(β)
colim = pushout[𝒟](α, β)
@test src(ob(colim)) == [1,1]
@test tgt(ob(colim)) == [2,1]
@test subpart(ob(colim), :vlabel) == [:u, :v]
@test subpart(ob(colim), :elabel) == [:e, :f]

α′ = ACSetTransformation(V=[2], E=Int[], g0, g)
@test !is_natural(α′) # Vertex labels don't match.
@test_throws ErrorException pushout[𝒟](α′, β)

end # module
