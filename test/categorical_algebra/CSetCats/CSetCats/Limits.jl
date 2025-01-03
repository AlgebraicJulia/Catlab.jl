module TestCSetCatLimits

using Catlab, Test

const 𝒞 = ACSetCategory(CSetCat(Graph()))

###################
# Terminal object #
###################
g = path_graph(Graph, 2)

T = terminal[𝒞]()
@test ob(T) == @acset Graph begin V=1; E=1; src=1; tgt=1 end
@test force(delete[𝒞](g); cat=𝒞) == ACSetTransformation(g, ob(T); V=[1,1], E=[1], cat=𝒞)

############
# Products #
############

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
α = ACSetTransformation((V=[2,3], E=[2]), I, g)
β = ACSetTransformation((V=[1,1], E=[2]), I, loop2)
γ = pair[𝒞](lim, α, β)
@test force(compose[𝒞](γ, proj1(lim)); cat=𝒞) == α
@test force(compose[𝒞](γ, proj2(lim)); cat=𝒞) == β

# Equalizer
###########

# Equalizer in Graph from (Reyes et al 2004, p. 50).
g, h = cycle_graph(Graph, 2), @acset Graph begin V=2;E=3; src=[1,2,2]; tgt=[2,1,1] end
ϕ = ACSetTransformation((V=[1,2], E=[1,2]), g, h)
ψ = ACSetTransformation((V=[1,2], E=[1,3]), g, h)
@test is_natural(ϕ, cat=𝒞) && is_natural(ψ, cat=𝒞)
eq = equalizer[𝒞](ϕ, ψ)
@test ob(eq) == I
@test force(incl(eq)[:V]) == FinFunction([1,2])
@test force(incl(eq)[:E]) == FinFunction([1], 2)


end # module
