module TestTransformations 
using Catlab, Test 
using .ThCategory

α = id[Cat2()](F)

@test (dom[Cat2()](α), codom[Cat2()](α)) == (F, F)

@test component(α, x) == id(ob_map(F,x))

end # module 
