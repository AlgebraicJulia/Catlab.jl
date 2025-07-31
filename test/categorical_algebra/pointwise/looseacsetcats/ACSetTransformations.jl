module TestLooseACSetTransformations

using Catlab, Test

const WGF = WeightedGraph{Float64}

g = path_graph(WGF, 2, E=(weight=2.,))
h = path_graph(WGF, 4, E=(weight=[1.,2.,3.],))

const 𝒞 = ACSetCategory(LooseACSetCat(WGF()))
half = x->x/2
α = ACSetTransformation((V=[1,2], E=[1], Weight=half,), g, h; cat=𝒞)
@test α[:Weight] isa SetFunction

α′ = ACSetTransformation(g, h, V=[1,2], E=[1], Weight=half, cat=𝒞)
@test α == α′
@test components(α)[:Weight](10.0) == 5.0
@test is_natural(α)
@test contains(sprint(show, α), "Weight =")

const WGB = WeightedGraph{Bool}
const 𝒟 = ACSetCategory(LooseACSetCat(WGB()))
g = star_graph(WeightedGraph{Bool}, 3, E=(weight=[true,false],))
α = ACSetTransformation((V=[2,1,3], E=[2,1], Weight=~,), g, g; cat=𝒟)
@test is_natural(α)
α² = compose[𝒟](α, α)
@test α²[:V] ≃ id[FinSetC()](FinSet(3))
@test α²[:Weight](true) == true

end # module
