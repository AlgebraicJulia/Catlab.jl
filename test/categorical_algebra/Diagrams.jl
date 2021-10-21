module TestDiagrams
using Test

using Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheorySymmetricGraph

const SchSGraph = TheorySymmetricGraph

# Diagrams
##########

# Diagram for paths of length 2.
C = FinCat(@acset Graph begin
  V = 3
  E = 2
  src = [1,2]
  tgt = [3,3]
end)
D = FinDomFunctor([:E,:E,:V], [:tgt,:src], C, FinCat(SchSGraph))
d = Diagram(D)
@test shape(d) == C

# Diagram morphisms
###################

f = DiagramHom([(2,:inv), (1,:inv), 3], [2,1], d, d)
@test dom(f) == d
@test codom(f) == d
@test is_functorial(shape_map(f))
@test shape_map(f) == FinFunctor([2,1,3], [2,1], C, C)
ϕ = diagram_map(f)
@test is_natural(ϕ, check_equations=false)
@test ϕ[1] == SchSGraph[:inv]
@test ϕ[3] == id(SchSGraph[:V])
@test ob_map(f, 2) == (1, SchSGraph[:inv])
@test hom_map(f, 2) == Path(graph(C), 1)
f² = f⋅f
@test shape_map(f²) == FinFunctor(1:3, 1:2, C, C)

f = DiagramHom{op}([(2,:inv), (1,:inv), 3], [2,1], D, D)
ιV = FinDomFunctor([:V], FinCat(1), FinCat(SchSGraph))
g = DiagramHom{op}([(1,:src)], D, ιV)
@test dom(g) == Diagram{op}(D)
@test codom(g) == Diagram{op}(ιV)
@test compose(id(dom(g)), g) == g
@test compose(g, id(codom(g))) == g
@test is_natural(diagram_map(g))
fg = f⋅g
@test ob_map(fg, 1) == (2, SchSGraph[:inv]⋅SchSGraph[:src])

d = dom(f)
@test op(op(d)) == d
@test op(op(f)) == f
@test dom(op(g)) == Diagram{co}(ιV)
@test codom(op(g)) == Diagram{co}(D)
@test op(g) == DiagramHom{co}([(1,:src)], ιV, D)
@test op(g)⋅op(f) == op(f⋅g)

end
