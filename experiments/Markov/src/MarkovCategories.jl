module MarkovCategories
export ThMarkovCategory, FreeMarkovCategory,
  Ob, Hom, dom, codom, compose, ⋅, ∘, otimes, ⊗, braid, mcopy, Δ, delete, ◊,
  expectation, 𝔼

using Catlab.GATs, Catlab.Theories, Catlab.WiringDiagrams
import Catlab.GATs: show_latex
import Catlab.Theories: Ob, Hom, dom, codom, compose, ⋅, ∘, otimes, ⊗, braid,
  mcopy, Δ, delete, ◊

# Theories
###########

""" Theory of *Markov categories with expectation*
"""
@signature ThMarkovCategory{Ob,Hom} <: ThMonoidalCategoryWithDiagonals{Ob,Hom} begin
  expectation(M::(A → B))::(A → B) <= (A::Ob, B::Ob)
  @op (𝔼) := expectation
end

@syntax FreeMarkovCategory{ObExpr,HomExpr} ThMarkovCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

function show_latex(io::IO, expr::HomExpr{:expectation}; kw...)
  print(io, "\\mathbb{E}\\left(")
  show_latex(io, first(expr))
  print(io, "\\right)")
end

# Wiring diagrams
#################

mcopy(A::Ports{ThMarkovCategory}, n::Int) = implicit_mcopy(A, n)

function expectation(M::WiringDiagram{ThMarkovCategory})
  if nboxes(M) <= 1
    functor(M, identity, expectation_box)
  else
    singleton_diagram(ThMarkovCategory, expectation_box(M))
  end
end

expectation_box(box::AbstractBox) = BoxOp{:expectation}(box)
expectation_box(exp::BoxOp{:expectation}) = exp
expectation_box(junction::Junction) = junction

end
