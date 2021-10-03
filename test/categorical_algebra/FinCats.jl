module TestFinCats
using Test

using Catlab.CategoricalAlgebra, Catlab.Graphs

# Free categories
#################

g = Graph(2)
add_edges!(g, [1,1], [2,2])
C = FinCat(g)
@test graph(C) == g
@test Ob(C) == FinSet(2)

h = Graph(4)
add_edges!(h, [1,1,2,3], [2,3,4,4])
D = FinCat(h)
F = FinFunctor((V=[1,4], E=[[1,3], [2,4]]), C, D)
@test dom(F) == C
@test codom(F) == D
@test is_functorial(F)
@test Ob(F) == FinFunction([1,4], FinSet(4))

@test ob_map(F, 2) == 4
@test hom_map(F, 1) == Path(h, [1,3])
@test F(Vertex(2)) == Vertex(4)
@test F(Edge(1)) == Path(h, [1,3])

end
