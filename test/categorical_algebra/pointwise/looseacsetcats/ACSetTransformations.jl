module TestLooseACSetTransformations 

using Catlab, Test

g = path_graph(WeightedGraph{Float64}, 2, E=(weight=2,))
h = path_graph(WeightedGraph{Float64}, 4, E=(weight=[1,2,3],))

# Loose morphisms.
half = x->x/2
α = LooseACSetTransformation((V=[1,2], E=[1]), (Weight=half,), g, h)
α′ = ACSetTransformation(g, h, V=[1,2], E=[1], Weight=half,)
@test α == α′
@test α isa LooseACSetTransformation
@test type_components(α)[:Weight](10.0) == 5.0
@test is_natural(α)
@test contains(sprint(show, α), "Weight =")

g = star_graph(WeightedGraph{Bool}, 3, E=(weight=[true,false],))
α = LooseACSetTransformation((V=[2,1,3], E=[2,1]), (Weight=~,), g, g)
@test is_natural(α)
α² = compose(α, α)
@test α² isa LooseACSetTransformation
@test α²[:V] == force(id(FinSet(3)))
@test α²[:Weight](true) == true

end # module
