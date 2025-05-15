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

# Coproducts in Graph: unitality.
g = path_graph(Graph, 4)
colim = coproduct[𝒞](g, Graph())
@test ob(colim) == g
@test coproj1(colim)[:V].(1:4) ==  [1,2,3,4]
@test coproj1(colim)[:E].(1:3) ==  [1,2,3]
@test collect(coproj2(colim)[:V]) == Int[] == collect(coproj2(colim)[:V]) 


# Coproduct in Graph.
h = cycle_graph(Graph, 2)
colim = coproduct[𝒞](g, h)
coprod = ob(colim)
@test nv(coprod) == 6
@test src(coprod) == [1,2,3,5,6]
@test tgt(coprod) == [2,3,4,6,5]
α = ACSetTransformation((V=[1,2,1,2], E=[1,2,1]), g, h)
β = id[𝒞](h)
γ = copair[𝒞](colim, α, β)
@test force(compose[𝒞](coproj1(colim), γ)) == α
@test collect(compose[𝒞](coproj2(colim),γ)[:V]) == collect(β[:V])
@test collect(compose[𝒞](coproj2(colim),γ)[:E]) == collect(β[:E])

colim2 = coproduct[𝒞](g, h)
@test hash(colim2) == hash(colim)

# Other test
#-----------
g = path_graph(Graph, 2)
colim = coproduct[𝒞](g, g)
g0 = ob(colim)
@test (nv(g0), ne(g0)) == (2*nv(g), 2*ne(g))
f = ACSetTransformation((V=[2,3], E=[2]), g, path_graph(Graph, 4))
@test copair[𝒞](colim, f, f) == ACSetTransformation(
  (V=[2,3,2,3], E=[2,2]), g0, path_graph(Graph, 4))


CCM = TypedCatWithCoproducts(𝒞)
@withmodel CCM (⊕, mzero) begin 
  g3 = g ⊕ g ⊕ g
  @test (nv(g3), ne(g3)) == (6, 3)
  @test mzero() == Graph()
end

# Coequalizer
#############

I = path_graph(Graph, 2)

# Coequalizer in Graph: collapsing a segment to a loop.

α = ACSetTransformation((V=[1], E=Int[]), Graph(1), I)
β = ACSetTransformation((V=[2], E=Int[]), Graph(1), I)
@test is_natural(α, cat=𝒞) && is_natural(β, cat=𝒞)
coeq = coequalizer[𝒞](α, β)
@test ob(coeq) == ob(terminal[𝒞]())
@test force(proj(coeq)[:V]) == FinFunction([1,1])
@test force(proj(coeq)[:E]) == FinFunction([1])

# Pushouts
###########

# Pushout in Graph from (Reyes et al 2004, p. 59).
α = ACSetTransformation((V=[2], E=Int[]), Graph(1), g)
β = ACSetTransformation((V=[1], E=Int[]), Graph(1), ob(terminal[𝒞]()))
@test is_natural(α) && is_natural(β)
colim = pushout[𝒞](α, β)
@test nv(ob(colim)) == 2
@test src(ob(colim)) == [1,2]
@test tgt(ob(colim)) == [2,2]
@test is_natural(coproj1(colim)) && is_natural(coproj2(colim))

# Free Graphs
#############

# Same pushout using generic colimit interface.
#diagram = FreeDiagram([Graph(1), g, ob(terminal(Graph))], [(α,1,2), (β,1,3)])
# ^ This diagram gives colimit that is isomorphic but not equal!
diagram = specialize(FreeDiagram(FreeGraph([g, ob(terminal[𝒞]()), Graph(1)], [(α,3,1), (β,3,2)]))) |> getvalue
ι1, ι2 = colim′ = colimit[𝒞](diagram)
@test ob(colim′) == ob(colim)
@test force(ι1) == force(coproj1(colim))
@test force(ι2) == force(coproj2(colim))

end # module
