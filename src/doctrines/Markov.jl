export MarkovCategory, FreeMarkovCategory, expectation, 𝔼

""" Doctrine of *Markov category*
"""
@signature MonoidalCategoryWithDiagonals(Ob,Hom) => MarkovCategory(Ob,Hom) begin
  expectation(M::Hom(A,B))::Hom(A,B) <= (A::Ob, B::Ob)

  # Unicode syntax
  𝔼(M::Hom) = expectation(M)
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
