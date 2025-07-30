module TestCSetTransformations 

using Catlab, Test 

# Constructors and accessors.
g, h = path_graph(Graph, 4), cycle_graph(Graph, 2)
α = ACSetTransformation((V=[1,2,1,2], E=[1,2,1]), g, h)
@test components(α) == (V=α[:V], E=α[:E])
@test α[:V] isa FinFunction{Int} && α[:E] isa FinFunction{Int}
@test α[:V](3) == 1
@test α[:E](2) == 2
@test startswith(sprint(show, α), "ACSetTransformation((V = ")

α′ = ACSetTransformation(g, h, V=[1,2,1,2], E=[1,2,1])
@test components(α′) == components(α)
α′′ = ACSetTransformation(g, h, V=FinFunction([1,2,1,2]), E=FinFunction([1,2,1]))
@test components(α′′) == components(α)

# Naturality.
d = naturality_failures(α)
@test [collect(d[a]) for a in keys(d)] == [[],[]]
@test is_natural(α)
β = ACSetTransformation((V=[1,2,1,2], E=[1,1,1]), g, h)
d = naturality_failures(β)
@test sort([collect(v) for v in values(d)]) == [[(2,1,2)],[(2,2,1)]]
@test startswith(sprint(show_naturality_failures, β), "Failures")
@test !is_natural(β)
β = ACSetTransformation((V=[2,1], E=[2,1]), h, h)
@test is_natural(β)
β = ACSetTransformation((V=[2,1], E=[2,2]), h, h)

# Category of C-sets.
@test dom(α) === g
@test codom(α) === h
γ = compose(α,β)
@test γ isa ACSetTransformation
@test γ == ACSetTransformation((V=α[:V]⋅β[:V], E=α[:E]⋅β[:E]), g, h)
@test id(g) isa TightACSetTransformation
@test force(compose(id(g), α)) == α
@test force(compose(α, id(h))) == α

# Injectivity / surjectivity.
G = @acset Graph begin V=2; E=1; src=1; tgt=2 end
H = @acset Graph begin V=2; E=2; src=1; tgt=2 end
I = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[1,2] end
f_ = homomorphism(G, H; monic=true, any=true)
g_ = homomorphism(H, G)
h_ = homomorphism(G, I; initial=(V=[1,1],))
@test is_monic(f_)
@test !is_epic(f_)
@test !is_monic(g_)
@test is_epic(g_)
@test !is_monic(h_)
@test !is_epic(h_)
@test_throws ErrorException homomorphism(H,G,monic=true,error_failures=true)



# cartesian transformations
##########################

#test on Petri nets in honor of Joachim Kock
@present SchPetri(FreeSchema) begin
  (S,T,I,O)::Ob
  is::Hom(I,S); it::Hom(I,T); os::Hom(O,S); ot::Hom(O,T)
end

@acset_type Petri(SchPetri,index=[:it,:ot])

p = @acset Petri begin
  S = 2; T = 2; I = 3; O = 4
  is = [1,1,1]; os = [2,2,2,2]
  it = [1,2,2]; ot = [1,1,1,2]
end
homoms = homomorphisms(p,p)
hs = [:it,:ot]
#Cartesian morphisms have to preserve the states and transitions and
#can only permute the inputs to T 2 and the outputs to T 1
@test sum(h->is_cartesian(h,hs),homoms) == 12

end # module
