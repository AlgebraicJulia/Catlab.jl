module TestCSetFunctors 

using Catlab, Test
CollageCat(infer_acset_cat(Graph()))

V,E,src′,tgt′ = generators(SchGraph)

# Reflexive graph as set-valued functor on a category with equations.
𝒞, 𝒟 = FinCat(SchGraph), FinCat(SchReflexiveGraph)
G_refl = FinDomFunctor(path_graph(ReflexiveGraph, 3))
@test is_functorial(G_refl)
F = FinDomFunctor(Dict(V=>V, E=>E), Dict(src′=>src′, tgt′=>tgt′), 𝒞, 𝒟;
                  homtype=:generator)
G = compose[CatC()](F, G_refl)
@test dom(G) == FinCat(SchGraph)
@test codom(G) == codom(G_refl)
@test ob_map(G, V) == FinSetInt(3)
@test hom_map(G, src′) == FinFunction([1,2,3,1,2], 3)
# @test startswith(sprint(show, G), "compose(")

# Graph homomorphisms as natural transformations.
g = parallel_arrows(Graph, 2)
add_edges!(g, [2,2], [2,2])
F = FinDomFunctor(path_graph(Graph, 3))
G = FinDomFunctor(g)
α = Transformation(Dict(V=>FinFunction([1,2,2]), 
                        E=>FinFunction([1,3],4)), F, G)
@test dom_ob(α) == 𝒞
@test getvalue(codom_ob(α)) isa CollageCat
@test is_natural(α)
@test α[V](3) == 2
# @test startswith(sprint(show, α), "FinTransformation(")

α_op = op(α)
# @test α_op isa FinTransformationMap
@test dom(α_op) == op(G)
@test codom(α_op) == op(F)
@test op(α_op) == α

function eq_trans(t::Transformation, u::Transformation)
  dom(t) == dom(u) || error("Bad dom")
  codom(t) == codom(u) || error("Bad codom")
  for o in ob_generators(dom(dom(t)))
    force(component(t, o)) == force(component(u, o)) || error("Bad $o component")
  end
  true
end

i2 = id[SkelFinSet()](FinSetInt(2))
swap = Transformation(Dict(V=>i2, E=>FinFunction([2,1,4,3])), G, G)
σ² = compose[Cat2()](swap, swap)
expected = Transformation(Dict(V=>i2, E=>FinFunction([1,2,3,4])), G, G)
@test eq_trans(σ², expected)
αswap = compose[Cat2()](α,swap)
expected = Transformation(Dict(V=>FinFunction([1,2,2]), 
                               E=>FinFunction([2,4])), 
                          F, G)
@test eq_trans(αswap, expected)

# Pullback data migration by pre-whiskering.
ιV = FinFunctor([V], FinCat(1), FinCat(SchGraph))
αV = @withmodel Cat2() (*) begin 
  ιV * α
end
@test ob_map(dom(αV), 1) == ob_map(F, V)
@test ob_map(codom(αV), 1) == ob_map(G, V)
@test component(αV, 1) == component(α, V)

# Post-whiskering and horizontal composition.
ιE = FinFunctor([E], FinCat(1), FinCat(SchGraph))
ϕ = Transformation([src′], ιE, ιV)

@withmodel Cat2() (*, ⋅) begin 
  @test is_natural(ϕ)
  @test component(ϕ*F, 1) == hom_map(F, src′)
  @test component(ϕ*α, 1) == compose[FinSetC()](hom_map(F, src′), α[V])
end

end # module
