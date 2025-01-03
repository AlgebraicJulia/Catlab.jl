module TestACSetTransformations 

using Test, Catlab


# Constructors and accessors.
#---------------------------
g, h = path_graph(Graph, 4), cycle_graph(Graph, 2)
α = ACSetTransformation((V=[1,2,1,2], E=[1,2,1]), g, h)
@test components(α) == (V=α[:V], E=α[:E])

@test α[:V] isa FinFunction && α[:E] isa FinFunction
@test α[:V](3) == 1
@test α[:E](2) == 2

@test startswith(sprint(show, α), "ACSetTransformation((V = ")

α′ = ACSetTransformation(g, h, V=[1,2,1,2], E=[1,2,1])
@test components(α′) == components(α)
α′′ = ACSetTransformation(g, h, V=FinFunction([1,2,1,2]), E=FinFunction([1,2,1]))
@test components(α′′) == components(α)

# Naturality.
#-------------

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

# Injectivity / surjectivity.
#----------------------------

G = @acset Graph begin V=2; E=1; src=1; tgt=2 end
H = @acset Graph begin V=2; E=2; src=1; tgt=2 end
I = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[1,2] end
f_ = ACSetTransformation(G, H; V=[1,2], E=[1])
g_ = ACSetTransformation(H, G; V=[1,2], E=[1,1])
h_ = ACSetTransformation(G, I; V=[1,1], E=[1])
@test all(is_natural, [f_, g_, h_])
@test is_monic(f_)
@test !is_epic(f_)
@test !is_monic(g_)
@test is_epic(g_)
@test !is_monic(h_)
@test !is_epic(h_)

end # module
