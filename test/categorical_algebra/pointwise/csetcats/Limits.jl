module TestCSetCatLimits

using Catlab, Test

const 𝒞 = ACSetCategory(CSetCat(Graph()))

###################
# Terminal object #
###################
g = path_graph(Graph, 2)

T = terminal[𝒞]()
@test ob(T) == @acset Graph begin V=1; E=1; src=1; tgt=1 end
@test force(delete[𝒞](g); cat=𝒞) == ACSetTransformation(
  g, ob(T); V=[1,1], E=[1], cat=𝒞)

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

  
# Product in Graph: two directed intervals (Reyes et al 2004, p. 48).
I = path_graph(Graph, 2)
prod′ = ob(product[𝒞](I, I))
@test (nv(prod′), ne(prod′)) == (4, 1)
@test src(prod′) != tgt(prod′)

CM = TypedCatWithProducts(𝒞)
@withmodel CM (⊗, munit) begin 
  I3 = I ⊗ I ⊗ I
  @test (nv(I3), ne(I3)) == (8, 1)
  @test munit() == apex(terminal[𝒞]())
end

# Product in Graph: deleting edges by multiplying by an isolated vertex.
g = path_graph(Graph, 4)
g0 = ob(product[𝒞](g, Graph(1)))
@test (nv(g0), ne(g0)) == (nv(g), 0)

# Equalizer
###########

# Equalizer in Graph from (Reyes et al 2004, p. 50).
g = cycle_graph(Graph, 2)
h = @acset Graph begin V=2;E=3; src=[1,2,2]; tgt=[2,1,1] end
ϕ = ACSetTransformation((V=[1,2], E=[1,2]), g, h)
ψ = ACSetTransformation((V=[1,2], E=[1,3]), g, h)
@test is_natural(ϕ, cat=𝒞) && is_natural(ψ, cat=𝒞)
eq = equalizer[𝒞](ϕ, ψ)
@test ob(eq) == I
@test force(incl(eq)[:V]) == FinFunction([1,2])
@test force(incl(eq)[:E]) == FinFunction([1], 2)


# Pullbacks 
###########

# Pullback in Graph from (Reyes et al 2004, p. 53).
# This test exposes an error in the text: using their notation, there should be
# a second edge between the vertices (1,3) and (1,4).
g0 = @acset Graph begin V=2; E=3; src=[1,1,2]; tgt=[1,2,2] end
g1 = @acset Graph begin V=3; E=3; src=[1,2,3]; tgt=[2,3,3] end
g2 = @acset Graph begin V=2; E=3; src=[1,2,2]; tgt=[1,2,2] end
ϕ = ACSetTransformation((V=[1,2,2], E=[2,3,3]), g1, g0)
ψ = ACSetTransformation((V=[1,2], E=[1,3,3]), g2, g0)
@test is_natural(ϕ) && is_natural(ψ)
lim = pullback[𝒞](ϕ, ψ)
@test nv(ob(lim)) == 3
@test sort!(collect(zip(src(ob(lim)), tgt(ob(lim))))) ==
  [(2,3), (2,3), (3,3), (3,3)]
@test is_natural(proj1(lim)) && is_natural(proj2(lim))

# Free Graphs 
#############

# Same pullback as above, using generic limit interface.
diagram = specialize(FreeGraph([g1, g2, g0], [(ϕ,1,3), (ψ,2,3)]) |> FreeDiagram)
π1, π2 = lim′ = limit[𝒞](diagram |> getvalue)

@test ob(lim′) == ob(lim)
@test force(π1) == force(proj1(lim))
@test force(π2) == force(proj2(lim))

end # module
