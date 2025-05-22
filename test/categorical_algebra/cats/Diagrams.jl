module TestDiagrams

using Test, Catlab

const SchSGraph = SchSymmetricGraph

# Diagram for paths of length 2.
#-------------------------------
C = FinCat(@acset Graph begin 
  V = 3 ; E = 2 ; src = [1,2] ; tgt = [3,3]
end)
Cod = FinCat(SchSGraph)
(V, E), (s, t, inv) = ob_generators(Cod), hom_generators(Cod)
D = FinDomFunctor([E,E,V], [t,s], C, Cod; homtype=:generator)
d = Diagram(D)

@test shape(d) == C
@test ob_map(d, 3) == SchSGraph[:V]
@test gen_map(d, 1) == SchSGraph[:tgt]
@test first.(collect_ob(d)) == [:E,:E,:V]
@test first.(collect_hom(d)) == [:tgt,:src]

d′ = Diagram(FinDomFunctor([E,E,V], [t,s], deepcopy(C), Cod; homtype=:generator))
@test hash(d) == hash(d′)

# Diagram morphisms in covariant diagram category 
#------------------------------------------------
f = DiagramHom([(2,inv), (1,inv), 3], [2,1], d, d; homtype=:generator)

@test force(codom[DiagramIdCat()](f)) == force(d)
@test hash(f) == hash(DiagramHom([(2,inv), (1,inv), 3], [2,1], d, d; homtype=:generator))
@test is_functorial(shape_map(f))
@test shape_map(f) == FinFunctor([2,1,3], [2,1], C, C; homtype=:generator)
ϕ = diagram_map(f)
@test is_natural(ϕ, check_equations=false)
@test ϕ[1] == SchSGraph[:inv]
@test ϕ[3] == id(SchSGraph[:V])
@test ob_map(f, 2) == (1, SchSGraph[:inv])
@test gen_map(f, 2) == Path(Graph(C), 1)
@test sort(collect_ob(f)) == [(1, ϕ[2]), (2, ϕ[1]), (3, ϕ[3])]
@test collect_hom(f) == [Path(Graph(C), 2), Path(Graph(C), 1)]
f² = compose[DiagramIdCat()](f,f)
@test shape_map(f²) == FinFunctor(Dict(1=>1,2=>2,3=>3), Dict(1=>1,2=>2), C, C; 
                                  homtype=:generator)
@test hash(f) != hash(f²)
@test startswith(sprint(show, f), "DiagramHom(")

# Diagram morphisms considered in DiagramOp category
#---------------------------------------------------
d′ = DiagramOp(d)
f = DiagramHom([(2,inv), (1,inv), 3], [2,1], d′, d′; homtype=:generator)
ιV = DiagramOp(FinDomFunctor([V], FinCat(1), FinCat(SchSGraph)))
g = DiagramHom([(1,s)], d′, ιV; homtype=:generator);
@test is_natural(diagram_map(g))


function eq_functor(X,Y)
  C = dom(X)
  for o in ob_generators(C)
    Xo, Yo = ob_map(X, o), ob_map(Y, o)
    Xo == Yo || error("bad ob $o: $Xo≠$Yo")
  end
  for h in hom_generators(C)
   Xh, Yh = gen_map(X, h), gen_map(Y, h)
   Xh == Yh || error("bad hom $h $Xh ≠ $Yh")
  end
  return true
end
""" 
Check two diagrams are functionally equal (for when `force` isn't good 
enough)
"""
function eq_diagram(X, Y)
  eq_functor(shape_map(X), shape_map(Y)) || error("Bad shape map")
  dX, dY = diagram_map(X), diagram_map(Y)
  for (k, v) in components(dX)
    v == component(dY, k) || error("Diagram map $k: $v ≠ $(component(dY, k))") 
  end
  return true
end

@withmodel DiagramOpCat() (dom, codom, ⋅, id) begin
  @test dom(g) == d′
  @test codom(g) == ιV
  @test eq_diagram(id(dom(g)) ⋅ g, g)
  @test eq_diagram(g⋅id(codom(g)), g)
  fg = f⋅g
  @test ob_map(fg, 1) == (2, compose(SchSGraph[:inv],SchSGraph[:src]))
end

# Applying `op` to DiagramHoms
#-----------------------------
d = dom[DiagramOpCat()](f)
@test op(op(d)) == d
@test op(op(f)) == f
@test dom[DiagramIdCat()](op(f)) == op(codom[DiagramOpCat()](f))
@test codom[DiagramIdCat()](op(f)) == op(dom[DiagramOpCat()](f))
@test eq_diagram(
  compose[DiagramIdCat()](op(g),op(f)), 
  op(compose[DiagramOpCat()](f,g))
)

# Monads of diagrams
####################

C = FinCat(SchGraph)
d = munit(DiagramId, C, V)
@test is_discrete(shape(d))
@test only(collect_ob(d)) == SchGraph[:V]
f = munit(DiagramHom, C, s)
@test last(only(components(diagram_map(f)))) == SchGraph[:src]

end # module
