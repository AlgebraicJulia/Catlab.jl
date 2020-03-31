module MarkovCategories
export MarkovCategory, FreeMarkovCategory,
  Ob, Hom, dom, codom, compose, ⋅, ∘, otimes, ⊗, braid, mcopy, Δ, delete, ◊,
  expectation, 𝔼

using Catlab.GAT, Catlab.Syntax, Catlab.Doctrines, Catlab.WiringDiagrams
import Catlab.Syntax: show_latex
import Catlab.Doctrines: Ob, Hom, dom, codom, compose, ⋅, ∘, otimes, ⊗, braid,
  mcopy, Δ, delete, ◊

# Doctrines
###########

""" Doctrine of *Markov category*
"""
@signature MonoidalCategoryWithDiagonals(Ob,Hom) => MarkovCategory(Ob,Hom) begin
  expectation(M::(A → B))::(A → B) <= (A::Ob, B::Ob)
  @op (𝔼) := expectation
end

@syntax FreeMarkovCategory(ObExpr,HomExpr) MarkovCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end

function show_latex(io::IO, expr::HomExpr{:expectation}; kw...)
  print(io, "\\mathbb{E}\\left(")
  show_latex(io, first(expr))
  print(io, "\\right)")
end

# Wiring diagrams
#################

mcopy(A::Ports{MarkovCategory.Hom}, n::Int) = implicit_mcopy(A, n)

function expectation(M::WiringDiagram{MarkovCategory.Hom})
  if nboxes(M) <= 1
    functor(M, identity, expectation_box)
  else
    singleton_diagram(MarkovCategory.Hom, expectation_box(M))
  end
end

expectation_box(box::AbstractBox) = BoxOp{:expectation}(box)
expectation_box(exp::BoxOp{:expectation}) = exp
expectation_box(junction::Junction) = junction

end
