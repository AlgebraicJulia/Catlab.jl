module TestCSetLimits

using Catlab, Test

g = path_graph(Graph, 4)

# Terminal object in Graph: the self-loop.
term = cycle_graph(Graph, 1)
lim = terminal(Graph)
@test ob(lim) == term
@test force(delete(lim, g)) ==
  ACSetTransformation((V=fill(1,4), E=fill(1,3)), g, term)

# Products in Graph: unitality.
lim = product(g, term)
@test ob(lim) == g
@test force(proj1(lim)) == force(id(g))
@test force(proj2(lim)) ==
  ACSetTransformation((V=fill(1,4), E=fill(1,3)), g, term)

  
# Product in Graph: two directed intervals (Reyes et al 2004, p. 48).
I = path_graph(Graph, 2)
prod′ = ob(product(I, I))
@test (nv(prod′), ne(prod′)) == (4, 1)
@test src(prod′) != tgt(prod′)

I3 = ⊗([I,I,I])
@test (nv(I3), ne(I3)) == (8, 1)
@test ⊗(Graph[]) == apex(terminal(Graph))

# Product in Graph: deleting edges by multiplying by an isolated vertex.
g = path_graph(Graph, 4)
g0 = ob(product(g, Graph(1)))
@test (nv(g0), ne(g0)) == (nv(g), 0)

# Product in Graph: copying edges by multiplying by the double self-loop.
loop2 = Graph(1)
add_edges!(loop2, [1,1], [1,1])
lim = product(g, loop2)
g2 = ob(lim)
@test (nv(g2), ne(g2)) == (nv(g), 2*ne(g))
@test (src(g2), tgt(g2)) == (repeat(src(g), 2), repeat(tgt(g), 2))
α = ACSetTransformation((V=[2,3], E=[2]), I, g)
β = ACSetTransformation((V=[1,1], E=[2]), I, loop2)
γ = pair(lim, α, β)
@test force(γ⋅proj1(lim)) == α
@test force(γ⋅proj2(lim)) == β

# Equalizer in Graph from (Reyes et al 2004, p. 50).
g, h = cycle_graph(Graph, 2), Graph(2)
add_edges!(h, [1,2,2], [2,1,1])
ϕ = ACSetTransformation((V=[1,2], E=[1,2]), g, h)
ψ = ACSetTransformation((V=[1,2], E=[1,3]), g, h)
@test is_natural(ϕ) && is_natural(ψ)
eq = equalizer(ϕ, ψ)
@test ob(eq) == I
@test force(incl(eq)[:V]) == FinFunction([1,2])
@test force(incl(eq)[:E]) == FinFunction([1], 2)

# Pullback in Graph from (Reyes et al 2004, p. 53).
# This test exposes an error in the text: using their notation, there should be
# a second edge between the vertices (1,3) and (1,4).
g0, g1, g2 = Graph(2), Graph(3), Graph(2)
add_edges!(g0, [1,1,2], [1,2,2])
add_edges!(g1, [1,2,3], [2,3,3])
add_edges!(g2, [1,2,2], [1,2,2])
ϕ = ACSetTransformation((V=[1,2,2], E=[2,3,3]), g1, g0)
ψ = ACSetTransformation((V=[1,2], E=[1,3,3]), g2, g0)
@test is_natural(ϕ) && is_natural(ψ)
lim = pullback(ϕ, ψ)
@test nv(ob(lim)) == 3
@test sort!(collect(zip(src(ob(lim)), tgt(ob(lim))))) ==
  [(2,3), (2,3), (3,3), (3,3)]
@test is_natural(proj1(lim)) && is_natural(proj2(lim))

# Same pullback using generic limit interface.
diagram = FreeDiagram([g1, g2, g0], [(ϕ,1,3), (ψ,2,3)])
π1, π2, _ = lim′ = limit(diagram)
@test ob(lim′) == ob(lim)
@test force(π1) == force(proj1(lim))
@test force(π2) == force(proj2(lim))
lim′ = limit(FinDomFunctor(diagram))
@test ob(lim′) == ob(lim)

end # module
