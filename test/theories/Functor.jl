using Test
using Match
import Catlab.Theories: dom, codom

@present C1(FreeCategory) begin
  A::Ob
  B::Ob
  C::Ob
  f::Hom(A,B)
  g::Hom(A,B)
  h::Hom(B,C)
end

A,B,C = generators(C1,:Ob)
f,g,h = generators(C1,:Hom)

struct TypeF1 <: AbstractFunctor
end

dom(F::TypeF1) = C1
codom(F::TypeF1) = C1

(F::TypeF1)(x::ObExpr) = x

function (F::TypeF1)(morph::HomExpr{:generator})
  @match morph.args[1] begin
    :f => f
    :g => f
    :h => h
  end
end

F = TypeF1()

@test F(compose(g,h)) == compose(f,h)
