export ThMonoidalCategoryAdditive, ThSymmetricMonoidalCategoryAdditive,
  FreeSymmetricMonoidalCategoryAdditive, oplus, ⊕, mzero, swap,
  ThMonoidalCategoryWithCodiagonals, ThCocartesianCategory,
  FreeCocartesianCategory, plus, zero, copair, coproj1, coproj2,
  ThMonoidalCategoryWithBidiagonalsAdditive,
  ThSemiadditiveCategory, ThAdditiveCategory,
  mcopy, delete, pair, proj1, proj2, Δ, ◊, +, antipode,
  ThHypergraphCategoryAdditive

# Monoidal category
###################

""" Theory of *monoidal categories*, in additive notation

Mathematically the same as [`ThMonoidalCategory`](@ref) but with different
notation.
"""
@signature ThMonoidalCategoryAdditive <: ThCategory begin
  @op (⊕) := oplus
  oplus(A::Ob, B::Ob)::Ob
  oplus(f::(A → B), g::(C → D))::((A ⊕ C) → (B ⊕ D)) ⊣
    [A::Ob, B::Ob, C::Ob, D::Ob]
  mzero()::Ob
end

# Convenience constructors TODO FIX THIS
# oplus(xs::AbstractVector{T}) where T = isempty(xs) ? mzero(T) : foldl(oplus, xs)
# oplus(x, y, z, xs...) = oplus([x, y, z, xs...])

# Overload `collect` and `ndims` as for multiplicative monoidal categories.
collect(expr::ObExpr{:oplus}) = vcat(map(collect, args(expr))...)
collect(expr::E) where E <: ObExpr{:mzero} = Base.typename(E).wrapper[]
ndims(expr::ObExpr{:oplus}) = sum(map(ndims, args(expr)))
ndims(expr::ObExpr{:mzero}) = 0

function show_unicode(io::IO, expr::Union{ObExpr{:oplus},HomExpr{:oplus}}; kw...)
  show_unicode_infix(io, expr, "⊕"; kw...)
end
show_unicode(io::IO, expr::ObExpr{:mzero}; kw...) = print(io, "O")

function show_latex(io::IO, expr::Union{ObExpr{:oplus},HomExpr{:oplus}}; kw...)
  show_latex_infix(io, expr, "\\oplus"; kw...)
end
show_latex(io::IO, expr::ObExpr{:mzero}; kw...) = print(io, "O")

# Symmetric monoidal category
#############################

""" Theory of *symmetric monoidal categories*, in additive notation

Mathematically the same as [`ThSymmetricMonoidalCategory`](@ref) but with
different notation.
"""
@signature ThSymmetricMonoidalCategoryAdditive <:
    ThMonoidalCategoryAdditive begin
  swap(A::Ob, B::Ob)::Hom(oplus(A,B),oplus(B,A))
end

@symbolic_model FreeSymmetricMonoidalCategoryAdditive{ObExpr,HomExpr} ThSymmetricMonoidalCategoryAdditive begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

function show_latex(io::IO, expr::HomExpr{:swap}; kw...)
  show_latex_script(io, expr, "\\sigma")
end

# Cocartesian category
######################

""" Theory of *monoidal categories with codiagonals*

A monoidal category with codiagonals is a symmetric monoidal category equipped
with coherent collections of merging and creating morphisms (monoids).
Unlike in a cocartesian category, the naturality axioms need not be satisfied.

For references, see [`ThMonoidalCategoryWithDiagonals`](@ref).
"""
@theory ThMonoidalCategoryWithCodiagonals <:
    ThSymmetricMonoidalCategoryAdditive begin
  plus(A::Ob)::((A ⊕ A) → A)
  zero(A::Ob)::(mzero() → A)
  
  # Commutative monoid axioms.
  (plus(A) ⊕ id(A)) ⋅ plus(A) == (id(A) ⊕ plus(A)) ⋅ plus(A) ⊣ [A::Ob]
  (zero(A) ⊕ id(A)) ⋅ plus(A) == id(A) ⊣ [A::Ob]
  (id(A) ⊕ zero(A)) ⋅ plus(A) == id(A) ⊣ [A::Ob]
  plus(A) == swap(A,A) ⋅ plus(A) ⊣ [A::Ob]

  # Coherence axioms.
  plus(A⊕B) == (id(A) ⊕ swap(B,A) ⊕ id(B)) ⋅ (plus(A) ⊕ plus(B)) ⊣ [A::Ob, B::Ob]
  zero(A⊕B) == zero(A) ⊕ zero(B) ⊣ [A::Ob, B::Ob]
  plus(mzero()) == id(mzero())
  zero(mzero()) == id(mzero())
end

""" Theory of *cocartesian (monoidal) categories*

For the traditional axiomatization of coproducts, see
[`ThCategoryWithCoproducts`](@ref).
"""
@theory ThCocartesianCategory <: ThMonoidalCategoryWithCodiagonals begin
  copair(f::(A → C), g::(B → C))::((A ⊕ B) → C) ⊣ [A::Ob, B::Ob, C::Ob]
  coproj1(A::Ob, B::Ob)::(A → (A ⊕ B))
  coproj2(A::Ob, B::Ob)::(B → (A ⊕ B))

  # Definitions of copairing and coprojections.
  copair(f,g) == (f⊕g)⋅plus(C) ⊣ [A::Ob, B::Ob, C::Ob, f::(A → C), g::(B → C)]
  coproj1(A,B) == id(A)⊕zero(B) ⊣ [A::Ob, B::Ob]
  coproj2(A,B) == zero(A)⊕id(B) ⊣ [A::Ob, B::Ob]
  
  # Naturality axioms.
  plus(A)⋅f == (f⊕f)⋅plus(B) ⊣ [A::Ob, B::Ob, f::(A → B)]
  zero(A)⋅f == zero(B) ⊣ [A::Ob, B::Ob, f::(A → B)]
end

""" Syntax for a free cocartesian category.

In this syntax, the copairing and inclusion operations are defined using merging
and creation, and do not have their own syntactic elements. This convention
could be dropped or reversed.
"""
@symbolic_model FreeCocartesianCategory{ObExpr,HomExpr} ThCocartesianCategory begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)

  copair(f::Hom, g::Hom) = compose(oplus(f,g), plus(codom(f)))
  coproj1(A::Ob, B::Ob) = oplus(id(A), zero(B))
  coproj2(A::Ob, B::Ob) = oplus(zero(A), id(B))
end

function show_latex(io::IO, expr::HomExpr{:plus}; kw...)
  if length(args(expr)) >= 2
    show_latex_infix(io, expr, "+"; kw...)
  else
    show_latex_script(io, expr, "\\nabla")
  end
end

function show_latex(io::IO, expr::HomExpr{:zero}; kw...)
  show_latex_script(io, expr, "0")
end

# Additive category
###################

""" Theory of *monoidal categories with bidiagonals*, in additive notation

Mathematically the same as [`ThMonoidalCategoryWithBidiagonals`](@ref) but
written additively, instead of multiplicatively.
"""
@theory ThMonoidalCategoryWithBidiagonalsAdditive <:
    ThMonoidalCategoryWithCodiagonals begin
  mcopy(A::Ob)::(A → (A ⊕ A))
  @op (Δ) := mcopy
  delete(A::Ob)::(A → mzero())
  @op (◊) := delete
  
  # Commutative comonoid axioms.
  Δ(A) == Δ(A) ⋅ swap(A,A) ⊣ [A::Ob]
  Δ(A) ⋅ (Δ(A) ⊕ id(A)) == Δ(A) ⋅ (id(A) ⊕ Δ(A)) ⊣ [A::Ob]
  Δ(A) ⋅ (◊(A) ⊕ id(A)) == id(A) ⊣ [A::Ob]
  Δ(A) ⋅ (id(A) ⊕ ◊(A)) == id(A) ⊣ [A::Ob]
end

""" Theory of *semiadditive categories*

Mathematically the same as [`ThBiproductCategory`](@ref) but written additively,
instead of multiplicatively.
"""
@theory ThSemiadditiveCategory <:
    ThMonoidalCategoryWithBidiagonalsAdditive begin
  pair(f::(A → B), g::(A → C))::(A → (B ⊕ C)) ⊣ [A::Ob, B::Ob, C::Ob]
  copair(f::(A → C), g::(B → C))::((A ⊕ B) → C) ⊣ [A::Ob, B::Ob, C::Ob]
  proj1(A::Ob, B::Ob)::((A ⊕ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊕ B) → B)
  coproj1(A::Ob, B::Ob)::(A → (A ⊕ B))
  coproj2(A::Ob, B::Ob)::(B → (A ⊕ B))
  
  plus(f::(A → B), g::(A → B))::(A → B) ⊣ [A::Ob, B::Ob]

  # Naturality axioms.
  f⋅Δ(B) == Δ(A)⋅(f⊕f) ⊣ [A::Ob, B::Ob, f::(A → B)]
  f⋅◊(B) == ◊(A) ⊣ [A::Ob, B::Ob, f::(A → B)]
  plus(A)⋅f == (f⊕f)⋅plus(B) ⊣ [A::Ob, B::Ob, f::(A → B)]
  zero(A)⋅f == zero(B) ⊣ [A::Ob, B::Ob, f::(A → B)]
  
  # Bimonoid axioms. (These follow from naturality + coherence axioms.)
  plus(A)⋅Δ(A) == (Δ(A)⊕Δ(A)) ⋅ (id(A)⊕swap(A,A)⊕id(A)) ⋅ (plus(A)⊕plus(A)) ⊣ [A::Ob]
  plus(A)⋅◊(A) == ◊(A) ⊕ ◊(A) ⊣ [A::Ob]
  zero(A)⋅Δ(A) == zero(A) ⊕ zero(A) ⊣ [A::Ob]
  zero(A)⋅◊(A) == id(mzero()) ⊣ [A::Ob]
end

""" Theory of *additive categories*

An additive category is a biproduct category enriched in abelian groups. Thus,
it is a semiadditive category where the hom-monoids have negatives.
"""
@theory ThAdditiveCategory <: ThSemiadditiveCategory begin
  antipode(A::Ob)::(A → A)

  # Antipode axioms.
  antipode(A) ⋅ f == f ⋅ antipode(B) ⊣ [A::Ob, B::Ob, f::(A → B)]
  Δ(A)⋅(id(A)⊕antipode(A))⋅plus(A) == ◊(A)⋅zero(A) ⊣ [A::Ob]
  Δ(A)⋅(antipode(A)⊕id(A))⋅plus(A) == ◊(A)⋅zero(A) ⊣ [A::Ob]
end

# Hypergraph category
#####################

""" Theory of *hypergraph categories*, in additive notation

Mathematically the same as [`ThHypergraphCategory`](@ref) but with different
notation.
"""
@signature ThHypergraphCategoryAdditive <:
    ThSymmetricMonoidalCategoryAdditive begin
  # Supply of Frobenius monoids.
  mcopy(A::Ob)::(A → (A ⊕ A))
  @op (Δ) := mcopy
  delete(A::Ob)::(A → mzero())
  @op (◊) := delete
  mmerge(A::Ob)::((A ⊕ A) → A)
  @op (∇) := mmerge
  create(A::Ob)::(mzero() → A)
  @op (□) := create

  # Self-dual compact closed category.
  dunit(A::Ob)::(mzero() → (A ⊕ A))
  dcounit(A::Ob)::((A ⊕ A) → mzero())
  dagger(f::(A → B))::(B → A) ⊣ [A::Ob, B::Ob]
end
