module TestFinCats
using Test

using Catlab.CategoricalAlgebra, Catlab.Graphs

# Free categories
#################

g = parallel_arrows(Graph, 2)
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
@test collect_ob(F) == [1,4]
@test collect_hom(F) == [Path(h, [1,3]), Path(h, [2,4])]

g, h = path_graph(Graph, 3), path_graph(Graph, 5)
C, D = FinCat(g), FinCat(h)
F = FinFunctor([1,3,5], [[1,2],[3,4]], C, D)
@test is_functorial(F)
@test F(Path(g, [1,2])) == Path(h, [1,2,3,4])

# Free diagrams
###############

C = FinCat(parallel_arrows(Graph, 2))
f, g = FinFunction([1,3], 3), FinFunction([2,3], 3)
F = FinDomFunctor([FinSet(2), FinSet(3)], [f,g], C)
@test is_functorial(F)
@test dom(F) == C
@test codom(F) isa TypeCat{<:FinSet{Int},<:FinFunction{Int}}
@test ob_map(F, 1) == FinSet(2)
@test hom_map(F, 2) == g

# `FreeDiagrams` interop.
diagram = FreeDiagram(ParallelPair(f, g))
@test FreeDiagram(F) == diagram
@test FinDomFunctor(diagram) == F

# Diagram interface.
@test diagram_ob_type(F) <: FinSet{Int}
@test cone_objects(F) == [FinSet(2), FinSet(3)]
@test cocone_objects(F) == [FinSet(2), FinSet(3)]
@test ob(limit(F)) == FinSet(1)
@test ob(colimit(F)) == FinSet(2)

end
