module TestACSetColimits 

using Catlab, Test

@present SchVELabeledGraph <: SchGraph begin
  Label::AttrType; vlabel::Attr(V,Label); elabel::Attr(E,Label)
end

@acset_type VELabeledGraph(SchVELabeledGraph,index=[:src,:tgt]) <: AbstractGraph


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

# Dynamic ACSets
#################
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

end # module
