module TestCSets
using Test
using Random: seed!

using Catlab.GATs, Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra

seed!(100)

@present SchDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end
@acset_type DDS(SchDDS, index=[:Φ])

@present SchSetAttr(FreeSchema) begin
  X::Ob
  D::AttrType
  f::Attr(X,D)
end
@acset_type SetAttr(SchSetAttr)

# Sets interop
##############

g = Graph(6)
add_edges!(g, 2:4, 3:5)
@test FinSet(g, :V) == FinSet(6)
f = FinFunction(g, :V)
@test collect(f) == 1:6
# @test is_indexed(f)
f = FinFunction(g, :src)
@test codom(f) == FinSet(6)
@test collect(f) == 2:4
# @test is_indexed(f)

f = FinDomFunction(g, :E)
@test collect(f) == 1:3
# @test is_indexed(f)
f = FinDomFunction(g, :tgt)
@test codom(f) == TypeSet(Int)
@test collect(f) == 3:5
# @test is_indexed(f)

g = path_graph(WeightedGraph{Float64}, 3, E=(weight=[0.5, 1.5],))
@test TypeSet(g, :Weight) == TypeSet(Float64)
@test TypeSet(g, :V) == TypeSet(Int)
@test_throws ArgumentError TypeSet(g, :W)

f = FinDomFunction(g, :weight)
@test codom(f) == TypeSet(Float64)
@test collect(f) == [0.5, 1.5]

# Dynamic ACSets 
################

X,Y = [DynamicACSet("WG", SchWeightedGraph; type_assignment=Dict(:Weight=>Float64)) 
      for _ in 1:2]
add_parts!(X, :V, 2)
add_parts!(X, :E, 3; src=[1,1,2],tgt=[2,1,1,],weight=[4.,3.,4.])
add_parts!(Y, :V, 2)
add_part!(Y, :E; src=1, tgt=2, weight=4.)

f = ACSetTransformation(X,X; V=[1,2], E=[1,2,3])
@test is_natural(f)
@test !is_natural(ACSetTransformation(X,X; V=[2,1], E=[1,2,3])) # bad homs
@test !is_natural(ACSetTransformation(X,X; V=[1,1], E=[2,1,3])) # bad attrs
@test components(f) == (V=FinFunction([1,2]), E=FinFunction([1,2,3]), 
                        Weight=VarFunction{Float64}([], FinSet(0)))

g = ACSetTransformation(Y,X; V=[1,2], E=[1])
@test is_natural(g)
@test compose(g,f) |> force == g

G, H = [DynamicACSet("Grph",SchGraph) for _ in 1:2];
add_parts!(G, :V, 2); 
add_parts!(H,:V,2);
add_part!(G, :E; src=1, tgt=2)
add_parts!(H, :E,2; src=[1,2], tgt=[1,2])
hs = homomorphisms(G,H)
@test length(hs) == 2
@test all(is_natural, hs)

@test is_natural(id(G))

G, H, expected =[DynamicACSet("WG", SchWeightedGraph; type_assignment=Dict(:Weight=>Float64)) 
                 for _ in 1:3]
add_parts!(G, :V, 2); 
add_parts!(H, :V, 2);
add_parts!(expected, :V, 3);
add_part!(G, :E; src=1, tgt=2, weight=1.0)
add_parts!(H, :E,2; src=[1,2], tgt=[1,2], weight=1.0)
add_parts!(expected, :E, 3; src=[1,2,3], tgt=[1,2,3], weight=1.0)
h1,h2 = homomorphisms(G,H)
clim = colimit(Span(h1,h2));
@test apex(clim) == expected

# C-set morphisms
#################

# Constructors and accessors.
g, h = path_graph(Graph, 4), cycle_graph(Graph, 2)
α = CSetTransformation((V=[1,2,1,2], E=[1,2,1]), g, h)
@test components(α) == (V=α[:V], E=α[:E])
@test α[:V] isa FinFunction{Int} && α[:E] isa FinFunction{Int}
@test α[:V](3) == 1
@test α[:E](2) == 2
@test startswith(sprint(show, α), "ACSetTransformation((V = ")

α′ = CSetTransformation(g, h, V=[1,2,1,2], E=[1,2,1])
@test components(α′) == components(α)
α′′ = CSetTransformation(g, h, V=FinFunction([1,2,1,2]), E=FinFunction([1,2,1]))
@test components(α′′) == components(α)

# Naturality.
d = naturality_failures(α)
@test [collect(d[a]) for a in keys(d)] == [[],[]]
@test is_natural(α)
β = CSetTransformation((V=[1,2,1,2], E=[1,1,1]), g, h)
d = naturality_failures(β)
@test sort([collect(v) for v in values(d)]) == [[(2,1,2)],[(2,2,1)]]
@test startswith(sprint(show_naturality_failures, β), "Failures")
@test !is_natural(β)
β = CSetTransformation((V=[2,1], E=[2,1]), h, h)
@test is_natural(β)
β = CSetTransformation((V=[2,1], E=[2,2]), h, h)

# Category of C-sets.
@test dom(α) === g
@test codom(α) === h
γ = compose(α,β)
@test γ isa TightACSetTransformation
@test γ == CSetTransformation((V=α[:V]⋅β[:V], E=α[:E]⋅β[:E]), g, h)
@test id(g) isa TightACSetTransformation
@test force(compose(id(g), α)) == α
@test force(compose(α, id(h))) == α

# Injectivity / surjectivity.
G = @acset Graph begin V=2; E=1; src=1; tgt=2 end
H = @acset Graph begin V=2; E=2; src=1; tgt=2 end
I = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[1,2] end
f_ = homomorphism(G, H; monic=true)
g_ = homomorphism(H, G)
h_ = homomorphism(G, I)
@test is_monic(f_)
@test !is_epic(f_)
@test !is_monic(g_)
@test is_epic(g_)
@test !is_monic(h_)
@test !is_epic(h_)
@test_throws ErrorException homomorphism(H,G,monic=true,error_failures=true)

# Limits
#-------

# Terminal object in Graph: the self-loop.
term = cycle_graph(Graph, 1)
lim = terminal(Graph)
@test ob(lim) == term
@test force(delete(lim, g)) ==
  CSetTransformation((V=fill(1,4), E=fill(1,3)), g, term)

# Products in Graph: unitality.
lim = product(g, term)
@test ob(lim) == g
@test force(proj1(lim)) == force(id(g))
@test force(proj2(lim)) ==
  CSetTransformation((V=fill(1,4), E=fill(1,3)), g, term)

# Product in Graph: two directed intervals (Reyes et al 2004, p. 48).
I = path_graph(Graph, 2)
prod′ = ob(product(I, I))
@test (nv(prod′), ne(prod′)) == (4, 1)
@test src(prod′) != tgt(prod′)

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
α = CSetTransformation((V=[2,3], E=[2]), I, g)
β = CSetTransformation((V=[1,1], E=[2]), I, loop2)
γ = pair(lim, α, β)
@test force(γ⋅proj1(lim)) == α
@test force(γ⋅proj2(lim)) == β

# Equalizer in Graph from (Reyes et al 2004, p. 50).
g, h = cycle_graph(Graph, 2), Graph(2)
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

# Same pullback using generic limit interface.
diagram = FreeDiagram([g1, g2, g0], [(ϕ,1,3), (ψ,2,3)])
π1, π2, _ = lim′ = limit(diagram)
@test ob(lim′) == ob(lim)
@test force(π1) == force(proj1(lim))
@test force(π2) == force(proj2(lim))
lim′ = limit(FinDomFunctor(diagram))
@test ob(lim′) == ob(lim)

# Colimits
#---------

# Initial object in graph: the empty graph.
colim = initial(Graph)
@test ob(colim) == Graph()
@test create(colim, g) == CSetTransformation((V=Int[], E=Int[]), Graph(), g)

# Coproducts in Graph: unitality.
g = path_graph(Graph, 4)
colim = coproduct(g, Graph())
@test ob(colim) == g
@test force(coproj1(colim)) == force(id(g))
@test force(coproj2(colim)) ==
  CSetTransformation((V=Int[], E=Int[]), Graph(), g)

# Coproduct in Graph.
h = cycle_graph(Graph, 2)
colim = coproduct(g, h)
coprod = ob(colim)
@test nv(coprod) == 6
@test src(coprod) == [1,2,3,5,6]
@test tgt(coprod) == [2,3,4,6,5]
α = CSetTransformation((V=[1,2,1,2], E=[1,2,1]), g, h)
β = id(h)
γ = copair(colim, α, β)
@test force(coproj1(colim)⋅γ) == α
@test force(coproj2(colim)⋅γ) == force(β)

colim2 = coproduct(path_graph(Graph, 4), cycle_graph(Graph, 2))
@test hash(colim2) == hash(colim)

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

# Same pushout using generic colimit interface.
#diagram = FreeDiagram([Graph(1), g, ob(terminal(Graph))], [(α,1,2), (β,1,3)])
# ^ This diagram gives colimit that is isomorphic but not equal!
diagram = FreeDiagram([g, ob(terminal(Graph)), Graph(1)], [(α,3,1), (β,3,2)])
ι1, ι2, _ = colim′ = colimit(diagram)
@test ob(colim′) == ob(colim)
@test force(ι1) == force(coproj1(colim))
@test force(ι2) == force(coproj2(colim))

# Attributed C-set morphisms
############################

# Constructors and accessors. Test type conversion as well Int -> Float64
g = path_graph(WeightedGraph{Float64}, 2, E=(weight=2,))
h = path_graph(WeightedGraph{Float64}, 4, E=(weight=[1,2,3],))
α = ACSetTransformation((V=[2,3], E=[2]), g, h)
@test length(components(α)) == 3

# Naturality.
@test is_natural(α)
β = ACSetTransformation((V=[2,1], E=[2]), g, h)
@test !is_natural(β) # Preserves weight but not graph homomorphism
β = ACSetTransformation((V=[1,2], E=[1]), g, h)
@test !is_natural(β) # Graph homomorphism but does not preserve weight
β = ACSetTransformation((V=[1,3], E=[1]), g, h)
uns = naturality_failures(β)
@test collect(uns[:src]) == [] && collect(uns[:tgt]) == [(1,2,3)] &&
  collect(uns[:weight]) == [(1,1.0,2.0)]

# Loose morphisms.
α = LooseACSetTransformation((V=[1,2], E=[1]), (Weight=x->x/2,), g, h)
@test α isa LooseACSetTransformation
@test type_components(α)[:Weight](10.0) == 5.0
@test is_natural(α)
@test contains(sprint(show, α), "Weight =")

g = star_graph(WeightedGraph{Bool}, 3, E=(weight=[true,false],))
α = LooseACSetTransformation((V=[2,1,3], E=[2,1]), (Weight=~,), g, g)
@test is_natural(α)
α² = compose(α, α)
@test α² isa LooseACSetTransformation
@test α²[:V] == force(id(FinSet(3)))
@test α²[:Weight](true) == true

# Limits
#-------

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,
                           index=[:src,:tgt]) <: AbstractGraph

# Terminal labeled graph.
@test ob(terminal(VELabeledGraph)) == cycle_graph(VELabeledGraph{Tuple{}}, 1; E=(;elabel=[()]), V=(;vlabel=[()]))

# Product of labeled graphs.
g = path_graph(VELabeledGraph{Symbol}, 2, V=(vlabel=[:a,:b],), E=(elabel=:f,))
h = path_graph(VELabeledGraph{String}, 2, V=(vlabel=["x","y"],), E=(elabel="f",))
π1, π2 = lim = product(g, h)
prod′ = ob(lim)
@test prod′ isa VELabeledGraph{Tuple{Symbol,String}}
@test Set(prod′[:vlabel]) == Set([(:a, "x"), (:a, "y"), (:b, "x"), (:b, "y")])
@test only(prod′[:elabel]) == (:f, "f")
@test prod′[src(prod′,1), :vlabel] == (:a, "x")
@test prod′[tgt(prod′,1), :vlabel] == (:b, "y")
@test is_natural(π1) && is_natural(π2)
@test type_components(π1)[:Label]((:a, "x")) == :a
@test type_components(π2)[:Label]((:a, "x")) == "x"

# Pullback of weighted graphs.
g0 = WeightedGraph{Nothing}(2)
add_edges!(g0, 1:2, 1:2)
g = WeightedGraph{Int}(4)
add_edges!(g, [1,3], [2,4], weight=[+1, -1])
ϕ = LooseACSetTransformation((V=[1,1,2,2], E=[1,2]),(Weight=nothing,), g, g0)
ψ = LooseACSetTransformation((V=[2,2,1,1], E=[2,1]), (Weight=nothing,),g, g0)
pb = ob(pullback(ϕ, ψ))
@test (nv(pb), ne(pb)) == (8, 2)
@test Set(pb[:weight]) == Set([(+1, -1), (-1, +1)])

# Limit with LooseACSetTransformations 
A = @acset VELabeledGraph{Symbol} begin V=2; vlabel=[:a,:b] end;
B = @acset VELabeledGraph{Symbol} begin V=2; vlabel=[:q,:z] end;
C = @acset VELabeledGraph{Symbol} begin V=2; vlabel=[:x,:y] end;
ac = LooseACSetTransformation(
  Dict([:V=>[1,2]]),Dict([:Label=>FinFunction(Dict(:a=>:x,:b=>:y))]),A,C);
bc = LooseACSetTransformation(
  Dict([:V=>[1,1]]),Dict([:Label=>FinFunction(Dict(:q=>:x,:z=>:x))]),B,C);
@test all(is_natural,[ac,bc])
res = limit(Cospan(ac,bc); product_attrs=true);
@test all(is_natural,legs(res))
@test apex(res)[:vlabel] == [(:a,:q),(:a,:z)]

# Colimits
#---------

# Initial labeled graph.
@test ob(initial(VELabeledGraph{Symbol})) == VELabeledGraph{Symbol}()

# Coproduct of labeled graphs.
g = path_graph(VELabeledGraph{Symbol}, 2, V=(vlabel=[:u,:v],), E=(elabel=:e,))
h = cycle_graph(VELabeledGraph{Symbol}, 1, V=(vlabel=:u,), E=(elabel=:f,))
coprod = ob(coproduct(g, h))
@test subpart(coprod, :vlabel) == [:u, :v, :u]
@test subpart(coprod, :elabel) == [:e, :f]

# Pushout of labeled graph.
g0 = VELabeledGraph{Symbol}()
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

# Pushout with given type components.
A = @acset SetAttr{Symbol} begin X=2; f=[:a,:b] end
B = @acset SetAttr{Symbol} begin X=2; f=[:x,:y] end
C = @acset SetAttr{Symbol} begin X=1; f=[:z] end
β = LooseACSetTransformation((X=[1,2],), (D=FinFunction(Dict(:a=>:x,:b=>:y)),), A, B)
γ = LooseACSetTransformation((X=[1,1],), (D=FinFunction(Dict(:a=>:z,:b=>:z)),), A, C)
@test all(is_natural, (β,γ))
g = (D=FinFunction(Dict(:x=>:q, :y=>:q)),)
h = (D=FinFunction(Dict(:z=>:q)),)
colim = pushout(β, γ, type_components=[g,h])
@test all(is_natural, legs(colim))
@test ob(colim) == @acset(SetAttr{Symbol}, begin X=1; f=[:q] end)
h′ = (D=FinFunction(Dict(:z=>:b)),)
@test_throws ErrorException pushout(β, γ, type_components=[g,h′])

# Finding C-set morphisms
#########################

# Graphs
#-------

g, h = path_graph(Graph, 3), path_graph(Graph, 4)
homs = [CSetTransformation((V=[1,2,3], E=[1,2]), g, h),
        CSetTransformation((V=[2,3,4], E=[2,3]), g, h)]
@test homomorphisms(g, h) == homs
@test homomorphisms(g, h, alg=HomomorphismQuery()) == homs
@test !is_isomorphic(g, h)

I = ob(terminal(Graph))
α = CSetTransformation((V=[1,1,1], E=[1,1]), g, I)
@test homomorphism(g, I) == α
@test homomorphism(g, I, alg=HomomorphismQuery()) == α
@test !is_homomorphic(g, I, monic=true)
@test !is_homomorphic(I, h)
@test !is_homomorphic(I, h, alg=HomomorphismQuery())

# Graph homomorphism starting from partial assignment, e.g. vertex assignment.
α = CSetTransformation((V=[2,3,4], E=[2,3]), g, h)
@test homomorphisms(g, h, initial=(V=[2,3,4],)) == [α]
@test homomorphisms(g, h, initial=(V=Dict(1 => 2, 3 => 4),)) == [α]
@test homomorphisms(g, h, initial=(E=Dict(1 => 2),)) == [α]
# Inconsistent initial assignment.
@test !is_homomorphic(g, h, initial=(V=Dict(1 => 1), E=Dict(1 => 3)))
# Consistent initial assignment but no extension to complete assignment.
@test !is_homomorphic(g, h, initial=(V=Dict(1 => 2, 3 => 3),))

# Monic and iso on a componentwise basis.
g1, g2 = path_graph(Graph, 3), path_graph(Graph, 2)
add_edges!(g1, [1,2,3,2], [1,2,3,3])  # loops on each node and one double arrow
add_edge!(g2, 1, 2)  # double arrow
@test length(homomorphisms(g2, g1)) == 8 # each vertex + 1->2, and four for 2->3
@test length(homomorphisms(g2, g1, monic=[:V])) == 5 # remove vertex solutions
@test length(homomorphisms(g2, g1, monic=[:E])) == 2 # two for 2->3
@test length(homomorphisms(g2, g1, iso=[:E])) == 0

# Loose
s1 = SetAttr{Int}()
add_part!(s1, :X, f=1)
add_part!(s1, :X, f=1)
s2, s3 = deepcopy(s1), deepcopy(s1)
set_subpart!(s2, :f, [2,1])
set_subpart!(s3, :f, [20,10])
@test length(homomorphisms(s2,s3))==0
@test length(homomorphisms(s2,s3; type_components=(D=x->10*x,)))==1
@test homomorphism(s2,s3; type_components=(D=x->10*x,)) isa LooseACSetTransformation
@test length(homomorphisms(s1,s1; type_components=(D=x->x^x,)))==4

#Backtracking with monic and iso failure objects
g1, g2 = path_graph(Graph, 3), path_graph(Graph, 2)
rem_part!(g1,:E,2)
@test_throws ErrorException homomorphism(g1,g2;monic=true,error_failures=true)

# Symmetric graphs
#-----------------

g, h = path_graph(SymmetricGraph, 4), path_graph(SymmetricGraph, 4)
αs = homomorphisms(g, h)
@test all(is_natural(α) for α in αs)
@test length(αs) == 16
αs = isomorphisms(g, h)
@test length(αs) == 2
@test map(α -> collect(α[:V]), αs) == [[1,2,3,4], [4,3,2,1]]
g = path_graph(SymmetricGraph, 3)
@test length(homomorphisms(g, h, monic=true)) == 4

# Graph colorability via symmetric graph homomorphism.
# The 5-cycle has chromatic number 3 but the 6-cycle has chromatic number 2.
K₂, K₃ = complete_graph(SymmetricGraph, 2), complete_graph(SymmetricGraph, 3)
C₅, C₆ = cycle_graph(SymmetricGraph, 5), cycle_graph(SymmetricGraph, 6)
@test !is_homomorphic(C₅, K₂)
@test is_homomorphic(C₅, K₃)
@test is_natural(homomorphism(C₅, K₃))
@test is_homomorphic(C₆, K₂)
@test is_natural(homomorphism(C₆, K₂))

# Labeled graphs
#---------------

g = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:a,:b,:c,:d],))
h = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:c,:d,:a,:b],))
α = ACSetTransformation((V=[3,4,1,2], E=[3,4,1,2]), g, h)
@test homomorphism(g, h) == α
@test homomorphism(g, h, alg=HomomorphismQuery()) == α
h = cycle_graph(LabeledGraph{Symbol}, 4, V=(label=[:a,:b,:d,:c],))
@test !is_homomorphic(g, h)
@test !is_homomorphic(g, h, alg=HomomorphismQuery())

# Random
#-------

comps(x) = sort([k=>collect(v) for (k,v) in pairs(components(x))])
# same set of morphisms
K₆ = complete_graph(SymmetricGraph, 6)
hs = homomorphisms(K₆,K₆)
rand_hs = homomorphisms(K₆,K₆; random=true)
@test sort(hs,by=comps) == sort(rand_hs,by=comps) # equal up to order
@test hs != rand_hs # not equal given order
@test homomorphism(K₆,K₆) != homomorphism(K₆,K₆;random=true)

# As a macro
#-----------

g = cycle_graph(LabeledGraph{String}, 4, V=(label=["a","b","c","d"],))
h = cycle_graph(LabeledGraph{String}, 4, V=(label=["b","c","d","a"],))
α = @acset_transformation g h
β = @acset_transformation g h begin
  V = [4,1,2,3]
  E = [4,1,2,3]
end monic=true
γ = @acset_transformation g h begin end monic=[:V]
@test α[:V](1) == 4
@test α[:E](1) == 4
@test α == β == γ

x = @acset Graph begin
  V = 2
  E = 2
  src = [1,1]
  tgt = [2,2]
end
@test length(@acset_transformations x x) == length(@acset_transformations x x monic=[:V]) == 4
@test length(@acset_transformations x x monic = true) == 2
@test length(@acset_transformations x x begin V=[1,2] end monic = [:E]) == 2
@test length(@acset_transformations x x begin V = Dict(1=>1) end monic = [:E]) == 2
@test_throws ErrorException @acset_transformation g h begin V = [4,3,2,1]; E = [1,2,3,4] end

# Sub-C-sets
############

# Construct sub-C-sets.
X = path_graph(Graph, 4)
A = Subobject(X, V=[2,3,4], E=[2,3])
@test ob(A) == X
α = hom(A)
@test is_natural(α)
@test dom(α) == path_graph(Graph, 3)
@test codom(α) == X
A_pred = Subobject(X, V=[false,true,true,true], E=[false,true,true])
@test hom(A_pred) == α

# Lattice of sub-C-sets.
X = Graph(6)
add_edges!(X, [1,2,3,4,4], [3,3,4,5,6])
A, B = Subobject(X, V=1:4, E=1:3), Subobject(X, V=3:6, E=3:5)
@test A ∧ B |> force == Subobject(X, V=3:4, E=3:3) |> force
@test A ∨ B |> force == Subobject(X, V=1:6, E=1:5) |> force
@test ⊤(X) |> force == Subobject(X, V=1:6, E=1:5) |> force
@test ⊥(X) |> force == Subobject(X, V=1:0, E=1:0) |> force

# Bi-Heyting algebra of sub-C-sets.
#
# Implication in Graph (Reyes et al 2004, Sec 9.1, p. 139).
I = Graph(1)
Y = path_graph(Graph, 3) ⊕ path_graph(Graph, 2) ⊕ path_graph(Graph, 2)
add_vertex!(Y)
add_edge!(Y, 2, 8)
Z = cycle_graph(Graph, 1) ⊕ cycle_graph(Graph, 1)
ιY, ιZ = colim = pushout(CSetTransformation(I, Y, V=[3]),
                         CSetTransformation(I, Z, V=[1]))
B_implies_C, B = Subobject(ιY), Subobject(ιZ)
C = Subobject(ob(colim), V=2:5, E=2:3)
@test (B ⟹ C) |> force == B_implies_C |> force

# Subtraction in Graph (Reyes et al 2004, Sec 9.1, p. 144).
X = ob(colim)
C = Subobject(X, V=2:5, E=[2,3,ne(X)-1])
@test (B \ C) |> force == Subobject(X, V=[nv(X)], E=[ne(X)]) |> force

# Negation in Graph (Reyes et al 2004, Sec 9.1, p. 139-140).
X = cycle_graph(Graph, 1) ⊕ path_graph(Graph, 2) ⊕ cycle_graph(Graph, 4)
add_vertex!(X)
add_edge!(X, 4, 8)
A = Subobject(X, V=[2,3,4,5,8], E=[3,7])
neg_A = Subobject(X, V=[1,6,7], E=[1,5])
@test is_natural(hom(A)) && is_natural(hom(neg_A))
@test ¬A |> force == neg_A |> force
@test ¬neg_A |> force == Subobject(X, V=[2,3,4,5,8], E=[2,3,7]) |> force

# Non in Graph (Reyes et al 2004, Sec 9.1, p. 144).
X = path_graph(Graph, 5) ⊕ path_graph(Graph, 2) ⊕ cycle_graph(Graph, 1)
A = Subobject(X, V=[1,4,5], E=[4])
non_A = Subobject(X, V=setdiff(vertices(X), 5), E=setdiff(edges(X), 4))
@test ~A |> force == non_A |> force
@test ~non_A |> force == Subobject(X, V=[4,5], E=[4]) |> force

# Negation and non in DDS.
S₁ = DDS(); add_parts!(S₁, :X, 5, Φ=[3,3,4,5,5])
S₂ = DDS(); add_parts!(S₂, :X, 3, Φ=[2,3,3])
ι₁, ι₂ = colim = coproduct(S₁, S₂)
S = ob(colim)
A = Subobject(S, X=[3,4,5])
@test ¬A |> force == Subobject(ι₂)
@test ¬Subobject(ι₂) |> force == Subobject(ι₁)
@test ~A |> force == ⊤(S) |> force

# Image and preimage
g1 = path_graph(Graph, 2)
g2 = apex(coproduct(g1, g1))
g3 = @acset Graph begin V=2; E=3; src=[1,1,2]; tgt=[1,2,2] end
h = homomorphisms(g1,g2)[2] # V=[3,4], E=[2]
ϕ = homomorphism(g2,g3; initial=(V=[1,1,2,2],))
@test components(hom(h(g1))) == (
  V = FinFunction([3, 4], 2, 4), E = FinFunction([2], 1, 2))
@test preimage(h, g2) |> force == (top(g1) |> force)
@test preimage(h, Subobject(g2, V=[1])) |> force == bottom(g1) |> force
@test preimage(h, Subobject(g2, V=[3])) |> force == Subobject(g1, V=[1]) |> force
@test ϕ(h(g1)) == Subobject(g3, V=[2], E=[3])

# Preimage
G = path_graph(Graph, 1) ⊕ path_graph(Graph, 2) ⊕ path_graph(Graph, 3)
H = let Loop=apex(terminal(Graph)); Loop ⊕ Loop ⊕ Loop end
# Each path graph gets its own loop
f = homomorphism(G, H; initial=(V=Dict([1=>1,2=>2,4=>3]),))
for i in 1:3
  @test is_isomorphic(dom(hom(preimage(f, Subobject(H, V=[i],E=[i])))),
                      path_graph(Graph, i))
end

# Enumeration of subobjects 
G = path_graph(Graph, 3)
subG, subobjs = subobject_graph(G) |> collect
@test length(subobjs) == 13 # ⊤,2x •→• •,2x •→•, •••,3x ••, 3x •, ⊥
@test length(incident(subG, 13, :src)) == 13 # ⊥ is initial
@test length(incident(subG, 1, :src)) == 1 # ⊤ is terminal

# Graph and ReflexiveGraph should have same subobject structure
subG = subobject_graph(path_graph(Graph, 2)) |> first
subRG, sos = subobject_graph(path_graph(ReflexiveGraph, 2))
@test all(is_natural, hom.(sos))
@test is_isomorphic(subG, subRG)

# Partial overlaps 
G = path_graph(Graph, 2)
os = partial_overlaps(G,G)
@test length(os) == 7 # ⊤, ••, 4x •, ⊥

# Maximum Common C-Set
######################

"""
Searching for overlaps: •→•→•↺  vs ↻•→•→•
Two results: •→•→• || •↺ •→• 
"""
g1 = @acset WeightedGraph{Bool} begin 
  V=3; E=3; src=[1,1,2]; tgt=[1,2,3]; weight=[true,false,false]
end 
g2 = @acset WeightedGraph{Bool} begin 
  V=3; E=3; src=[1,2,3]; tgt=[2,3,3]; weight=[true,false,false] 
end 
(apx1, ((L1,),(R1,))), (apx2, ((L2,),(R2,))) = collect(maximum_common_subobject(g1, g2))
apex1 = @acset WeightedGraph{Bool} begin 
  V=3; E=2; Weight=2; src=[1,2]; tgt=[2,3]; weight=AttrVar.(1:2)
end
apex2 = @acset WeightedGraph{Bool} begin 
  V=3; E=2; Weight=2; src=[1,3]; tgt=[2,3]; weight=AttrVar.(1:2)
end
@test is_isomorphic(apx1, apex1)
@test collect(L1[:V]) == [1,2,3]
@test collect(R1[:V]) == [1,2,3]
@test L1(apx1) == Subobject(g1, V=[1,2,3], E=[2,3])

@test is_isomorphic(apx2, apex2)
@test collect(L2[:V]) == [1,2,3]
@test collect(R2[:V]) == [3,1,2]
@test L2(apx2) == Subobject(g1, V=[1,2,3], E=[1,3])

# AttrVars 
##########

const WG = WeightedGraph
A = @acset WG{Bool} begin V=1;E=2;Weight=2;src=1;tgt=1;weight=[AttrVar(1),true] end
B = @acset WG{Bool} begin V=1;E=2;Weight=1;src=1;tgt=1;weight=[true, false] end

@test VarFunction(A,:weight) == VarFunction{Bool}([AttrVar(1), true], FinSet(2))

f = ACSetTransformation(Dict(:V=>[1],:E=>[2,1],:Weight=>[false, AttrVar(1)]), A,B)
@test is_natural(f)
@test force(id(A) ⋅ f) == force(f) == force(f ⋅ id(B))
@test f isa TightACSetTransformation
@test_throws ErrorException ACSetTransformation(
  Dict(:V=>[1],:E=>[2,1],:Weight=>[false, AttrVar(5)]), A,B)

w1,w2,w3 = ws = [WG{x}() for x in [Symbol,Bool,Int]]
[add_parts!(w, :Weight, 2) for w in ws]
rem_part!(w1, :Weight, 1)
@test [nparts(w, :Weight) for w in ws] == [1,2,2]

# Construct Tight/Loose ACSet Transformations
#--------------------------------------------
f21 = LooseVarFunction{Bool,Symbol}([AttrVar(1),AttrVar(1)], x->Symbol(x), FinSet(1))
t21 = ACSetTransformation(Dict(:Weight=>f21), w2, w1) 
@test t21 isa LooseACSetTransformation
t22 = ACSetTransformation(Dict(:Weight=>[AttrVar(1),false]), w2, w2)


bool_to_sym(x::Bool)::Symbol = x ? :A : :B

f21 = LooseVarFunction{Bool,Symbol}([AttrVar(1),:X], bool_to_sym, FinSet(1))
l21 = ACSetTransformation((Weight = f21,), w2, w1)

t32 = LooseVarFunction{Int,Bool}([AttrVar(2),false], iseven,FinSet(2))
l32 = ACSetTransformation((Weight = t32,), w3, w2)
@test all(is_natural,[l21,l32])

# Composition 
#------------

@test collect((l32 ⋅ l21)[:Weight]) == [:X,:B]
l = l32 ⋅ l21 # {Int}->{Bool} x {Bool}->{Symbol} = {Int}->{Symbol}
@test collect(l[:Weight]) == [:X,:B]


# Homomorphism search
#####################

A = @acset WG{Bool} begin V=1;E=2;Weight=1;src=1;tgt=1;
                          weight=[true, AttrVar(1)] end
B = @acset WG{Bool} begin V=1;E=3;Weight=2;src=1;tgt=1;
                          weight=[true, false, AttrVar(2)] end
@test length(homomorphisms(A,B))==3 # E1 forced to E1, E2 can go anywhere

A = @acset WG{Bool} begin V=1;E=3;Weight=1;src=1;tgt=1;
                          weight=[false, AttrVar(1), AttrVar(1)] end
B = @acset WG{Bool} begin V=1;E=4;Weight=2;src=1;tgt=1;
                          weight=[false, true, true, AttrVar(2)] end
# E1 is forced to E1, E2 and E3 are forced to go to the same value
# so either false, AttrVar(2), or 4 choices for (true,true).
@test length(homomorphisms(A,B))== 6


# with a different C-set where different attributes affect each other
@present ThA2(FreeSchema) begin X::Ob; D::AttrType; (f,g)::Attr(X,D) end 
@acset_type A2(ThA2)
X = @acset A2{Symbol} begin X=2; D=2; f=[:A,AttrVar(1)]; g=[AttrVar(2), :B] end 
Y = @acset A2{Symbol} begin X=2; D=1; f=[:C,:A]; g=[:C; :B] end 
@test length(homomorphisms(X,Y)) == 1

X = @acset A2{Symbol} begin X=3; D=3; f=[:A,AttrVar(1),AttrVar(2)]; g=[AttrVar(2), :B, AttrVar(3)] end 
Y = @acset A2{Symbol} begin X=3; D=1; f=[:C,:A,:Z]; g=[:C, :B,:Z] end 
@test isempty(homomorphisms(X,Y))

@test length(homomorphisms(Y,Y;initial=(D=[:Q],)))==1

Z = @acset A2{Symbol} begin X=1; D=1; f=[AttrVar(1)]; g=[AttrVar(1)] end 
@test isnothing(homomorphism(Z,Z;initial=(D=[:Q],)))

# Colimits 
#---------
const WG = WeightedGraph

A = @acset WG{Bool} begin V=1;E=2;Weight=2;src=1;tgt=1;weight=[AttrVar(1),true] end

# CREATE 
@test dom(create(A)) == WG{Bool}()

# COPRODUCT
diagram = DiscreteDiagram([A,A])
AA = coproduct([A,A])
@test apex(AA)[:weight] == [AttrVar(1),true,AttrVar(3),true]
@test legs(AA)[2] isa TightACSetTransformation
@test collect(legs(AA)[2][:Weight]) == AttrVar.(3:4)

X = @acset WG{Bool} begin V=1;E=1;Weight=2;src=1;tgt=1;weight=[true] end
f′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(1)],))
g′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(2)],))
fg = universal(AA, Cospan(f′,g′))

# PUSHOUTS
V = @acset WG{Bool} begin Weight=1 end
f = ACSetTransformation(Dict(:Weight=>[AttrVar(1)]), V, A)
g = ACSetTransformation(Dict(:Weight=>[AttrVar(2)]), V, A)

clim = colimit(Span(f,g));
@test all(is_natural, legs(clim))
@test collect(legs(clim)[2][:Weight]) == AttrVar.([3,1]) # not [3,4] anymore

fg = universal(clim, Cospan(f′,g′))

f = ACSetTransformation(Dict(:Weight=>[AttrVar(1)]), V, A)
g = ACSetTransformation(Dict(:Weight=>[true]), V, A)

clim = colimit(Span(f,g));
@test all(is_natural, legs(clim))
@test apex(clim)[:weight] == [true,true,AttrVar(2),true]
@test collect(legs(clim)[1][:Weight]) == [true,AttrVar(1)]

# Subobjects with variables 

X = @acset SetAttr{Bool} begin X=2;D=1;f=[true, AttrVar(1)] end 
A = Subobject(X, X=[1])
B = Subobject(X, X=[2], D=[1])
@test A ∧ B |> force == ⊥(X) |> force
@test A ∨ B |> force == ⊤(X) |> force

end
