module TestPaths 

using Catlab, Test

p = Path{Int}(1,Int)

@test p isa Path{Int,Int,Vector{Int}}
@test length(p) == 0 
@test src(p) == 1 == tgt(p)

p2 = Path([10,20,30],1,2)

@test vcat(p, p2) == p2

G = path_graph(Graph, 3)

p3 = Path(G, [1])
p4 = Path(G, 2)
@test vcat(p3,p4) == Path(G,[1,2])

end # module
