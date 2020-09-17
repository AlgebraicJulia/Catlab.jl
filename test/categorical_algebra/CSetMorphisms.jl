module TestCSetMorphisms
using Test

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FinSets, Catlab.CategoricalAlgebra.Graphs
using Catlab.CategoricalAlgebra.Graphs: TheoryGraph

# C-set morphisms
#################

# Constructors and accessors.
g, h = Graph(4), Graph(2)
add_edges!(g, [1,2,3], [2,3,4])
add_edges!(h, [1,2], [2,1])
α = CSetTransformation((V=[1,2,1,2], E=[1,2,1]), g, h)
@test components(α) == (V=α[:V], E=α[:E])
@test α[:V] isa FinFunction{Int} && α[:E] isa FinFunction{Int}
@test α[:V](3) == 1
@test α[:E](2) == 2

α′ = CSetTransformation(g, h, V=[1,2,1,2], E=[1,2,1])
@test components(α′) == components(α)
α′′ = CSetTransformation(g, h, V=FinFunction([1,2,1,2]), E=FinFunction([1,2,1]))
@test components(α′′) == components(α)

# Naturality.
@test is_natural(α)
β = CSetTransformation((V=[1,2,1,2], E=[1,1,1]), g, h)
@test !is_natural(β)
β = CSetTransformation((V=[2,1], E=[2,1]), h, h)
@test is_natural(β)

# Category of C-sets.
@test dom(α) === g
@test codom(α) === h
@test compose(α,β) == CSetTransformation((V=α[:V]⋅β[:V], E=α[:E]⋅β[:E]), g, h)
@test force(compose(id(g), α)) == α
@test force(compose(α, id(h))) == α

# Limits
#-------

# Terminal object in Graph: the self-loop.
term = Graph(1)
add_edge!(term, 1, 1)
@test ob(terminal(Graph)) == term

# Products in Graph: unitality.
lim = product(g, term)
@test ob(lim) == g
@test force(proj1(lim)) == force(id(g))
@test force(proj2(lim)) ==
  CSetTransformation((V=fill(1,4), E=fill(1,3)), g, term)

# Product in Graph: two directed intervals (Reyes et al 2004, p. 48).
I = Graph(2)
add_edge!(I, 1, 2)
prod = ob(product(I, I))
@test nv(prod) == 4
@test ne(prod) == 1
@test src(prod) != tgt(prod)

# Product in Graph: deleting edges by multiplying by an isolated vertex.
g = Graph(4)
add_edges!(g, [1,2,3], [2,3,4])
g0 = ob(product(g, Graph(1)))
@test nv(g0) == nv(g)
@test ne(g0) == 0

# Product in Graph: copying edges by multiplying by the double self-loop.
cycle2 = Graph(1)
add_edges!(cycle2, [1,1], [1,1])
g2 = ob(product(g, cycle2))
@test nv(g2) == nv(g)
@test ne(g2) == 2*ne(g)
@test src(g2) == repeat(src(g), 2)
@test tgt(g2) == repeat(tgt(g), 2)

# Equalizer in Graph from (Reyes et al 2004, p. 50).
g, h = Graph(2), Graph(2)
add_edges!(g, [1,2], [2,1])
add_edges!(h, [1,2,2], [2,1,1])
ϕ = CSetTransformation((V=[1,2], E=[1,2]), g, h)
ψ = CSetTransformation((V=[1,2], E=[1,3]), g, h)
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
ϕ = CSetTransformation((V=[1,2,2], E=[2,3,3]), g1, g0)
ψ = CSetTransformation((V=[1,2], E=[1,3,3]), g2, g0)
@test is_natural(ϕ) && is_natural(ψ)
lim = pullback(ϕ, ψ)
@test nv(ob(lim)) == 3
@test sort!(collect(zip(src(ob(lim)), tgt(ob(lim))))) ==
  [(2,3), (2,3), (3,3), (3,3)]
@test is_natural(proj1(lim)) && is_natural(proj2(lim))

# Colimits
#---------

# Initial object in graph: the empty graph.
@test ob(initial(Graph)) == Graph()

# Coproducts in Graph: unitality.
g = Graph(4)
add_edges!(g, [1,2,3], [2,3,4])
colim = coproduct(g, Graph())
@test ob(colim) == g
@test force(coproj1(colim)) == force(id(g))
@test force(coproj2(colim)) ==
  CSetTransformation((V=Int[], E=Int[]), Graph(), g)

# Coproduct in Graph.
h = Graph(2)
add_edges!(h, [1,2], [2,1])
coprod = ob(coproduct(g, h))
@test nv(coprod) == 6
@test src(coprod) == [1,2,3,5,6]
@test tgt(coprod) == [2,3,4,6,5]

# Coequalizer in Graph: collapsing a segment to a loop.
g = Graph(2)
add_edge!(g, 1, 2)
α = CSetTransformation((V=[1], E=Int[]), Graph(1), g)
β = CSetTransformation((V=[2], E=Int[]), Graph(1), g)
@test is_natural(α) && is_natural(β)
coeq = coequalizer(α, β)
@test ob(coeq) == ob(terminal(Graph))
@test force(proj(coeq)[:V]) == FinFunction([1,1])
@test force(proj(coeq)[:E]) == FinFunction([1])

# Pushout in Graph from (Reyes et al 2004, p. 59).
α = CSetTransformation((V=[2], E=Int[]), Graph(1), g)
β = CSetTransformation((V=[1], E=Int[]), Graph(1), ob(terminal(Graph)))
@test is_natural(α) && is_natural(β)
colim = pushout(α, β)
@test nv(ob(colim)) == 2
@test src(ob(colim)) == [1,2]
@test tgt(ob(colim)) == [2,2]
@test is_natural(coproj1(colim)) && is_natural(coproj2(colim))

# Attributed C-set morphisms
############################

@present TheoryWeightedGraph <: TheoryGraph begin
  Weight::Data
  weight::Attr(E,Weight)
end
const WeightedGraph = ACSetType(TheoryWeightedGraph, index=[:src,:tgt])

# Constructors and accessors.
g, h = WeightedGraph{Float64}(2), WeightedGraph{Float64}(4)
add_edge!(g, 1, 2, weight=2.0)
add_edges!(h, [1,2,3], [2,3,4], weight=[1.0,2.0,3.0])
α = ACSetTransformation((V=[2,3], E=[2]), g, h)
@test length(components(α)) == 2

# Naturality.
@test is_natural(α)
β = ACSetTransformation((V=[2,1], E=[2]), g, h)
@test !is_natural(β) # Preserves weight but not graph homomorphism
β = ACSetTransformation((V=[1,2], E=[1]), g, h)
@test !is_natural(β) # Graph homomorphism but does not preserve weight

# Colimits
#---------

@present TheoryLabeledGraph <: TheoryGraph begin
  Label::Data
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end
const LabeledGraph = ACSetType(TheoryLabeledGraph, index=[:src,:tgt])

# Initial labeled graph.
@test ob(initial(LabeledGraph{Symbol})) == LabeledGraph{Symbol}()

# Coproduct of labeled graphs.
g = LabeledGraph{Symbol}()
add_vertices!(g, 2, vlabel=[:u,:v])
add_edge!(g, 1, 2, elabel=:e)
h = LabeledGraph{Symbol}()
add_vertex!(h, vlabel=:u)
add_edge!(h, 1, 1, elabel=:f)
coprod = ob(coproduct(g, h))
@test subpart(coprod, :vlabel) == [:u, :v, :u]
@test subpart(coprod, :elabel) == [:e, :f]

# Pushout of labeled graph.
g0 = LabeledGraph{Symbol}()
add_vertex!(g0, vlabel=:u)
α = ACSetTransformation((V=[1], E=Int[]), g0, g)
β = ACSetTransformation((V=[1], E=Int[]), g0, h)
@test is_natural(α) && is_natural(β)
colim = pushout(α, β)
@test src(ob(colim)) == [1,1]
@test tgt(ob(colim)) == [2,1]
@test subpart(ob(colim), :vlabel) == [:u, :v]
@test subpart(ob(colim), :elabel) == [:e, :f]

α′ = ACSetTransformation(V=[2], E=Int[], g0, g)
@test !is_natural(α′) # Vertex labels don't match.
@test_throws ErrorException pushout(α′, β)

end
