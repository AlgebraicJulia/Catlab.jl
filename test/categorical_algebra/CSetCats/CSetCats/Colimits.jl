module TestCSetCatColimits

using Catlab, Test 

const 𝒞 = ACSetCategory(CSetCat(Graph()))


# Initial object 
################

g = path_graph(Graph, 2)
I = initial[𝒞]()
@test ob(I) == Graph()
@test create[𝒞](g) == ACSetTransformation(Graph(), g; cat=𝒞)

# Coproducts
############

g = path_graph(Graph, 2)
colim = coproduct[𝒞](g, g)
g0 = ob(colim)
@test (nv(g0), ne(g0)) == (2*nv(g), 2*ne(g))
f = ACSetTransformation((V=[2,3], E=[2]), g, path_graph(Graph, 4), 𝒞)
@test copair[𝒞](colim, f, f) == ACSetTransformation(
  (V=[2,3,2,3], E=[2,2]), g0, path_graph(Graph, 4), 𝒞)



# Coequalizer
#############

I = path_graph(Graph, 2)

# Coequalizer in Graph: collapsing a segment to a loop.

α = ACSetTransformation((V=[1], E=Int[]), Graph(1), I, 𝒞)
β = ACSetTransformation((V=[2], E=Int[]), Graph(1), I, 𝒞)
@test is_natural(α, 𝒞) && is_natural(β, 𝒞)
coeq = coequalizer[𝒞](α, β)
@test ob(coeq) == ob(terminal[𝒞]())
@test force(proj(coeq)[:V]) == FinFunction([1,1])
@test force(proj(coeq)[:E]) == FinFunction([1])

end # module
