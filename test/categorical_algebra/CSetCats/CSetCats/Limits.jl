module TestCSetCatLimits

using Catlab, Test

const 𝒞 = ACSetCategory(CSetCat(Graph()))


# Terminal object
#################
g = path_graph(Graph, 2)

T = terminal[𝒞]()
@test ob(T) == @acset Graph begin V=1; E=1; src=1; tgt=1 end
@test force(𝒞, delete[𝒞](g)) == ACSetTransformation(g, ob(T); V=[1,1], E=[1], cat=𝒞)

# Products
###########

g = path_graph(Graph, 4)

g0 = ob(product[𝒞](g, Graph(1)))
@test (nv(g0), ne(g0)) == (nv(g), 0)

# Product in Graph: copying edges by multiplying by the double self-loop.
loop2 = @acset Graph begin V=1; E=2; src=1; tgt=1 end
lim = product[𝒞](g, loop2)
g2 = ob(lim)
@test (nv(g2), ne(g2)) == (nv(g), 2*ne(g))
@test (src(g2), tgt(g2)) == (repeat(src(g), 2), repeat(tgt(g), 2))

I = path_graph(Graph, 2)
α = ACSetTransformation((V=[2,3], E=[2]), I, g, 𝒞)
β = ACSetTransformation((V=[1,1], E=[2]), I, loop2, 𝒞)
γ = pair[𝒞](lim, α, β)
@test force(𝒞, compose[𝒞](γ, proj1(lim))) == α
@test force(𝒞, compose[𝒞](γ, proj2(lim))) == β

# Equalizer
###########

# Equalizer in Graph from (Reyes et al 2004, p. 50).
g, h = cycle_graph(Graph, 2), @acset Graph begin V=2;E=3; src=[1,2,2]; tgt=[2,1,1] end
ϕ = ACSetTransformation((V=[1,2], E=[1,2]), g, h, 𝒞)
ψ = ACSetTransformation((V=[1,2], E=[1,3]), g, h, 𝒞)
@test is_natural(ϕ, 𝒞) && is_natural(ψ, 𝒞)
eq = equalizer[𝒞](ϕ, ψ)
@test ob(eq) == I
@test force(incl(eq)[:V]) == FinFunction([1,2])
@test force(incl(eq)[:E]) == FinFunction([1], 2)


end # module
