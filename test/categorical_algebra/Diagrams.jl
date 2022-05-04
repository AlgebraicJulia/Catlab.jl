module TestDiagrams
using Test

using Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheoryGraph, TheorySymmetricGraph

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
@test ob_map(d, 3) == SchSGraph[:V]
@test hom_map(d, 1) == SchSGraph[:tgt]
@test first.(collect_ob(d)) == [:E,:E,:V]
@test first.(collect_hom(d)) == [:tgt,:src]
@test startswith(sprint(show, d), "Diagram{id}(")
@test hash(D) != hash(Diagram{op}(D))

# Diagram morphisms
###################

f = DiagramHom([(2,:inv), (1,:inv), 3], [2,1], d, d)
@test dom(f) == d
@test codom(f) == d
@test hash(f) == hash(DiagramHom([(2,:inv), (1,:inv), 3], [2,1], d, d))
@test is_functorial(shape_map(f))
@test shape_map(f) == FinFunctor([2,1,3], [2,1], C, C)
ϕ = diagram_map(f)
@test is_natural(ϕ, check_equations=false)
@test ϕ[1] == SchSGraph[:inv]
@test ϕ[3] == id(SchSGraph[:V])
@test ob_map(f, 2) == (1, SchSGraph[:inv])
@test hom_map(f, 2) == Path(graph(C), 1)
@test collect_ob(f) == [(2, ϕ[1]), (1, ϕ[2]), (3, ϕ[3])]
@test collect_hom(f) == [Path(graph(C), 2), Path(graph(C), 1)]
f² = f⋅f
@test shape_map(f²) == FinFunctor(1:3, 1:2, C, C)
@test hash(f) != hash(f²)

f = DiagramHom{op}([(2,:inv), (1,:inv), 3], [2,1], D, D)
ιV = FinDomFunctor([:V], FinCat(1), FinCat(SchSGraph))
g = DiagramHom{op}([(1,:src)], D, ιV)
@test dom(g) == Diagram{op}(D)
@test codom(g) == Diagram{op}(ιV)
@test compose(id(dom(g)), g) == g
@test compose(g, id(codom(g))) == g
@test is_natural(diagram_map(g))
@test startswith(sprint(show, f), "DiagramHom{op}(")

fg = f⋅g
@test ob_map(fg, 1) == (2, SchSGraph[:inv]⋅SchSGraph[:src])

d = dom(f)
@test op(op(d)) == d
@test op(op(f)) == f
@test dom(op(f)) == op(codom(f))
@test codom(op(f)) == op(dom(f))
@test op(g)⋅op(f) == op(f⋅g)

# Monads of diagrams
####################

C = FinCat(TheoryGraph)
d = munit(Diagram{id}, C, :V)
@test is_discrete(shape(d))
@test only(collect_ob(d)) == TheoryGraph[:V]
f = munit(DiagramHom{id}, C, :src)
@test only(components(diagram_map(f))) == TheoryGraph[:src]

end
