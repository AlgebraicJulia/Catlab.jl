module TestACSetLimits 

using Test, Catlab

############
# CSetCats #
############
const 𝒞 = ACSetCategory(CSetCat(Graph()))

# Initial object 
################
g = path_graph(Graph, 2)
I = initial[𝒞]()
@test ob(I) == Graph()
@test create[𝒞](g) == ACSetTransformation(Graph(), g; cat=𝒞)

# Terminal object
#################

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

# Coproducts
############

g = path_graph(Graph, 2)
colim = coproduct[𝒞](g, g)
g0 = ob(colim)
@test (nv(g0), ne(g0)) == (2*nv(g), 2*ne(g))
f = ACSetTransformation((V=[2,3], E=[2]), g, path_graph(Graph, 4), 𝒞)
@test copair[𝒞](colim, f, f) == ACSetTransformation(
  (V=[2,3,2,3], E=[2,2]), g0, path_graph(Graph, 4), 𝒞)

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

# Coequalizer
#############

# Coequalizer in Graph: collapsing a segment to a loop.

α = ACSetTransformation((V=[1], E=Int[]), Graph(1), I, 𝒞)
β = ACSetTransformation((V=[2], E=Int[]), Graph(1), I, 𝒞)
@test is_natural(α, 𝒞) && is_natural(β, 𝒞)
coeq = coequalizer[𝒞](α, β)
@test ob(coeq) == ob(T)
@test force(proj(coeq)[:V]) == FinFunction([1,1])
@test force(proj(coeq)[:E]) == FinFunction([1])

#############
# ACSetCats #
#############

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,index=[:src,:tgt]) <: AbstractGraph

const VES = VELabeledGraph{Symbol}
const 𝒟 = ACSetCategory(ACSetCat(VES()))

@test ob(initial[𝒟]()) == VES()

g = @acset VES begin V=2; E=1; src=1; tgt=2; vlabel=[:a,:b]; elabel=[:e] end

@test create[𝒟](g) == ACSetTransformation(VES(), g; cat=𝒟)

expected =  @acset VES begin V=4; E=2; src=[1,3]; tgt=[2,4]; vlabel=[:a,:b,:a,:b]; elabel=[:e,:e] end

@test expected == ob(coproduct[𝒟](g,g)) # replace with is_isomorphic once that's working


# VarACSets
###########


const 𝒱 = ACSetCategory(VarACSetCat(VES()))

g = @acset VES begin V=2; E=2; Label=2; src=1; tgt=2; vlabel=[AttrVar(1),:b]; elabel=[:e, AttrVar(2)] end

expected = @acset VES begin 
  V=4; E=4; Label=4; src=[1,1,3,3]; tgt=[2,2,4,4]
  vlabel=[AttrVar(1),:b,AttrVar(3),:b]; 
  elabel=[:e,AttrVar(2),:e,AttrVar(4)] 
end
@test ob(coproduct[𝒱](g,g)) == expected

end # module
