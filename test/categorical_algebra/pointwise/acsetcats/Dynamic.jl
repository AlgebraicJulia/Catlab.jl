module TestDynamicACSets 

using Catlab, Test


G, H, expected =[DynamicACSet("WG", SchWeightedGraph; type_assignment=Dict(:Weight=>Float64)) 
                 for _ in 1:3]
add_parts!(G, :V, 2); 
add_parts!(H, :V, 2);
add_parts!(expected, :V, 3);
add_part!(G, :E; src=1, tgt=2, weight=1.0)
add_parts!(H, :E,2; src=[1,2], tgt=[1,2], weight=1.0)
add_parts!(expected, :E, 3; src=[1,2,3], tgt=[1,2,3], weight=1.0)
h1,h2 = homomorphisms(G,H)

Grph = ACSetCategory(G)

clim = colimit[Grph](Span(h1,h2));
@test apex(clim) == expected

end # module
