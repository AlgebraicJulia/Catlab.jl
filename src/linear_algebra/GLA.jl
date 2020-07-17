module GraphicalLinearAlgebra
export LinearFunctions, FreeLinearFunctions,
  LinearRelations, FreeLinearRelations,
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, swap,
  dagger, dunit, docunit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  plus, +, zero, coplus, cozero, meet, top, join, bottom,
  scalar, antipode, antipode, adjoint, evaluate

import Base: adjoint
using AutoHashEquals
using Requires

using ...Catlab, ...Theories
import ...Theories:
  Ob, Hom, dom, codom, compose, ⋅, ∘, id, oplus, ⊕, mzero, swap,
  dagger, dunit, dcounit, mcopy, Δ, delete, ◊, mmerge, ∇, create, □,
  plus, +, zero, coplus, cozero, meet, top, join, bottom
using ...Programs
import ...Programs: evaluate_hom

# Theories
###########

""" Theory of *linear functions*, aka linear maps

Functional fragment of graphical linear algebra.
"""
@theory SemiadditiveCategory(Ob,Hom) => LinearFunctions(Ob,Hom) begin
  adjoint(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)
  
  scalar(A::Ob, c::Number)::(A → A)
  antipode(A::Ob)::(A → A)

  # Scalar and antipode axioms.
  scalar(A, a) ⋅ scalar(A, b) == scalar(A, a*b) ⊣ (A::Ob, a::Number, b::Number)
  scalar(A, 1) == id(A) ⊣ (A::Ob)
  scalar(A, a) ⋅ Δ(A) == Δ(A) ⋅ (scalar(A, a) ⊕ scalar(A, a)) ⊣ (A::Ob, a::Number)
  scalar(A, a) ⋅ ◊(A) == ◊(A) ⊣ (A::Ob, a::Number)
  Δ(A) ⋅ (scalar(A, a) ⊕ scalar(A, b)) ⋅ plus(A) == scalar(A, a+b) ⊣ (A::Ob, a::Number, b::Number)
  scalar(A, 0) == ◊(A) ⋅ zero(A) ⊣ (A::Ob)
  zero(A) ⋅ scalar(A, a) == zero(A) ⊣ (A::Ob, a::Number)
  antipode(A) == scalar(A, -1) ⊣ (A::Ob)

  # Homogeneity axiom. Additivity is inherited from `SemiadditiveCategory`.
  scalar(A, c) ⋅ f == f ⋅ scalar(B, c) ⊣ (A::Ob, B::Ob, c::Number, f::(A → B))
end

@syntax FreeLinearFunctions(ObExpr,HomExpr) LinearFunctions begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = new(f,g; strict=true) # No normalization!
end

""" Theory of *linear relations*

The full relational language of graphical linear algebra.
"""
@theory AbelianBicategoryRelations(Ob,Hom) => LinearRelations(Ob,Hom) begin
  adjoint(R::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)

  scalar(A::Ob, c::Number)::(A → A)
  antipode(A::Ob)::(A → A)

  # Linearity axioms.
  plus(A)⋅R == (R⊕R)⋅plus(B) ⊣ (A::Ob, B::Ob, R::(A → B))
  zero(A)⋅R == zero(B) ⊣ (A::Ob, B::Ob, R::(A → B))
  scalar(A, c) ⋅ R == R ⋅ scalar(B, c) ⊣ (A::Ob, B::Ob, c::Number, R::(A → B))
end

@syntax FreeLinearRelations(ObExpr,HomExpr) LinearRelations begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(R::Hom, S::Hom) = associate(new(R,S))
  compose(R::Hom, S::Hom) = new(R,S; strict=true) # No normalization!
end

# Evaluation
############

function evaluate_hom(f::FreeLinearFunctions.Hom{:generator}, xs::Vector;
                      generators::AbstractDict=Dict())
  M = generators[f]
  x = reduce(vcat, xs; init=eltype(M)[])
  [ M*x ]
end

function evaluate_hom(f::FreeLinearFunctions.Hom{:plus}, xs::Vector; kw...)
  if first(f) isa ObExpr
    # Addition map.
    [ reduce(+, xs) ]
  else
    # Sum of linear maps.
    mapreduce(+, args(f)) do g
      evaluate_hom(g, xs; kw...)
    end
  end
end
function evaluate_hom(f::FreeLinearFunctions.Hom{:zero}, xs::Vector;
                      generators::AbstractDict=Dict())
  map(collect(codom(f))) do A
    dims = generators[A]
    zeros(dims...)
  end
end

evaluate_hom(f::FreeLinearFunctions.Hom{:scalar}, xs::Vector; kw...) = last(f) .* xs
evaluate_hom(f::FreeLinearFunctions.Hom{:antipode}, xs::Vector; kw...) = -1 .* xs

# Extras
########

function __init__()
  @require LinearMaps="7a12625a-238d-50fd-b39a-03d52299707e" begin
    include("LinearMapsExternal.jl")
  end
  @require LinearOperators="5c8ed15e-5a4c-59e4-a42b-c7e8811fb125" begin
    include("LinearOperatorsExternal.jl")
  end
end

end
