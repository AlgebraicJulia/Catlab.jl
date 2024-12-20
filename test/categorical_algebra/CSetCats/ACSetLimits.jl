module TestACSetLimits 

using Test, Catlab

C = ACSetCategory(CSetCat(Graph()))
Grph = Category(TypeCat(CatOfACSet(C)))
g = path_graph(Graph, 2)
h = cycle_graph(Graph, 1)
f = ACSetTransformation(g, h; V=[1,1], E=[1], cat=C)

Xs = [g,g]
P = product(CatWithProducts(C),DiscreteDiagram(Xs))

T = terminal(CatWithProducts(C))


unpack(C, FreeDiagram(Span(f,f)))


colimit(C, DiscreteDiagram([g, g]))

end # module
