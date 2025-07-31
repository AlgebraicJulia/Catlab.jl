module TestTransformations 

using Catlab, Test
using .ThCategory

function eq_trans(t::Transformation, u::Transformation)
  dom(t) == dom(u) || error("Bad dom")
  codom(t) == codom(u) || error("Bad codom")
  for o in ob_generators(dom(dom(t)))
    force(component(t, o)) == force(component(u, o)) || error("Bad $o component")
  end
  true
end

# 1-category of functors and natural transformations
####################################################
𝒞 = Category(FinSetC())
C = FinCat(path_graph(Graph, 2))
F = FinDomFunctor([FinSet(4), FinSet(2)], [FinFunction([1,1,2,2])], C, 𝒞)

# Commutative square as natural transformation.
α₀, α₁ = FinFunction([3,4,1,2]), FinFunction([2,1])

α = Transformation([α₀, α₁], F, F)
@test is_natural(α)
@test (α[1], α[2]) == (α₀, α₁)
@test components(α) == Dict(1=>α₀, 2=>α₁)
expected = Transformation([FinFunction(1:4), FinFunction(1:2)], F, F)
@test eq_trans(compose[Cat2()](α,α), expected)


# 2-category of categories, functors, and natural transformations
#################################################################
α = id[Cat2()](F)

@test (dom[Cat2()](α), codom[Cat2()](α)) == (F, F)

@test component(α, 1) == id(𝒞, ob_map(F,1))

end # module 
