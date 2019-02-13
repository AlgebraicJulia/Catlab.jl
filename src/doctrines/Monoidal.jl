export MonoidalCategory, otimes, munit, ⊗, collect, ndims,
  SymmetricMonoidalCategory, FreeSymmetricMonoidalCategory, braid,
  MonoidalCategoryWithDiagonals, CartesianCategory, FreeCartesianCategory,
  mcopy, delete, pair, proj1, proj2, Δ, ◇,
  MonoidalCategoryWithCodiagonals, CocartesianCategory, FreeCocartesianCategory,
  mmerge, create, copair, incl1, incl2, ∇, □,
  MonoidalCategoryWithBidiagonals, BiproductCategory, FreeBiproductCategory,
  CartesianClosedCategory, FreeCartesianClosedCategory, hom, ev, curry,
  CompactClosedCategory, FreeCompactClosedCategory, dual, dunit, dcounit,
  DaggerCategory, FreeDaggerCategory, dagger,
  DaggerCompactCategory, FreeDaggerCompactCategory

import Base: collect, ndims

# Monoidal category
###################

""" Doctrine of *monoidal category*

To avoid associators and unitors, we assume the monoidal category is *strict*.
By the coherence theorem there is no loss of generality, but we may add a
signature for weak monoidal categories later.
"""
@signature Category(Ob,Hom) => MonoidalCategory(Ob,Hom) begin
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::Hom(A,B), g::Hom(C,D))::Hom(otimes(A,C),otimes(B,D)) <=
    (A::Ob, B::Ob, C::Ob, D::Ob)
  munit()::Ob
  
  # Unicode syntax
  ⊗(A::Ob, B::Ob) = otimes(A, B)
  ⊗(f::Hom, g::Hom) = otimes(f, g)
end

# Convenience constructors
otimes(xs::Vector{T}) where T = isempty(xs) ? munit(T) : foldl(otimes, xs)
otimes(x, y, z, xs...) = otimes([x, y, z, xs...])

""" Collect generators of object in monoidal category as a vector.
"""
collect(expr::ObExpr) = [ expr ]
collect(expr::ObExpr{:otimes}) = vcat(map(collect, args(expr))...)
collect(expr::ObExpr{:munit}) = roottypeof(expr)[]
roottypeof(x) = typeof(x).name.wrapper

""" Number of "dimensions" of object in monoidal category.
"""
ndims(expr::ObExpr) = 1
ndims(expr::ObExpr{:otimes}) = sum(map(ndims, args(expr)))
ndims(expr::ObExpr{:munit}) = 0

function show_unicode(io::IO, expr::ObExpr{:otimes}; kw...)
  Syntax.show_unicode_infix(io, expr, "⊗"; kw...)
end
function show_unicode(io::IO, expr::HomExpr{:otimes}; kw...)
  Syntax.show_unicode_infix(io, expr, "⊗"; kw...)
end
show_unicode(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

function show_latex(io::IO, expr::ObExpr{:otimes}; kw...)
  Syntax.show_latex_infix(io, expr, "\\otimes"; kw...)
end
function show_latex(io::IO, expr::HomExpr{:otimes}; kw...)
  Syntax.show_latex_infix(io, expr, "\\otimes"; kw...)
end
show_latex(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

# Symmetric monoidal category
#############################

""" Doctrine of *symmetric monoidal category*

The signature (but not the axioms) is the same as a braided monoidal category.
"""
@signature MonoidalCategory(Ob,Hom) => SymmetricMonoidalCategory(Ob,Hom) begin
  braid(A::Ob, B::Ob)::Hom(otimes(A,B),otimes(B,A))
end

@syntax FreeSymmetricMonoidalCategory(ObExpr,HomExpr) SymmetricMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

function show_latex(io::IO, expr::HomExpr{:braid}; kw...)
  Syntax.show_latex_script(io, expr, "\\sigma")
end

# Cartesian category
####################

""" Doctrine of *monoidal category with diagonals*

A monoidal category with diagonals is a symmetric monoidal category equipped
with coherent collections of copying and deleting morphisms (comonoids).
Unlike in a cartesian category, the naturality axioms need not be satisfied.

References:

- Selinger, 2010, "A survey of graphical languages for monoidal categories",
  Section 6.6: "Cartesian center"
- Selinger, 1999, "Categorical structure of asynchrony"
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => MonoidalCategoryWithDiagonals(Ob,Hom) begin
  mcopy(A::Ob)::Hom(A,otimes(A,A))
  delete(A::Ob)::Hom(A,munit())
  
  # Unicode syntax
  Δ(A::Ob) = mcopy(A)
  ◇(A::Ob) = delete(A)
end

""" Doctrine of *cartesian category*

Actually, this is a cartesian *symmetric monoidal* category but we omit these
qualifiers for brevity.
"""
@signature MonoidalCategoryWithDiagonals(Ob,Hom) => CartesianCategory(Ob,Hom) begin
  pair(f::Hom(A,B), g::Hom(A,C))::Hom(A,otimes(B,C)) <= (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::Hom(otimes(A,B),A)
  proj2(A::Ob, B::Ob)::Hom(otimes(A,B),B)
end

""" Syntax for a free cartesian category.

In this syntax, the pairing and projection operations are defined using
duplication and deletion, and do not have their own syntactic elements.
Of course, this convention could be reversed.
"""
@syntax FreeCartesianCategory(ObExpr,HomExpr) CartesianCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  
  pair(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g))
  proj1(A::Ob, B::Ob) = otimes(id(A), delete(B))
  proj2(A::Ob, B::Ob) = otimes(delete(A), id(B))
end

function show_latex(io::IO, expr::HomExpr{:mcopy}; kw...)
  Syntax.show_latex_script(io, expr, "\\Delta")
end
function show_latex(io::IO, expr::HomExpr{:delete}; kw...)
  Syntax.show_latex_script(io, expr, "\\lozenge")
end

# Cocartesian category
######################

""" Doctrine of *monoidal category with codiagonals*

A monoidal category with codiagonals is a symmetric monoidal category equipped
with coherent collections of merging and creating morphisms (monoids).
Unlike in a cocartesian category, the naturality axioms need not be satisfied.

For references, see `MonoidalCategoryWithDiagonals`.
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => MonoidalCategoryWithCodiagonals(Ob,Hom) begin
  mmerge(A::Ob)::Hom(otimes(A,A),A)
  create(A::Ob)::Hom(munit(),A)

  # Unicode syntax
  ∇(A::Ob) = mmerge(A)
  □(A::Ob) = create(A)
end

""" Doctrine of *cocartesian category*

Actually, this is a cocartesian *symmetric monoidal* category but we omit these
qualifiers for brevity.
"""
@signature MonoidalCategoryWithCodiagonals(Ob,Hom) => CocartesianCategory(Ob,Hom) begin
  copair(f::Hom(A,C), g::Hom(B,C))::Hom(otimes(A,B),C) <= (A::Ob, B::Ob, C::Ob)
  incl1(A::Ob, B::Ob)::Hom(A,otimes(A,B))
  incl2(A::Ob, B::Ob)::Hom(B,otimes(A,B))
end

""" Syntax for a free cocartesian category.

In this syntax, the copairing and inclusion operations are defined using
merging and creation, and do not have their own syntactic elements.
Of course, this convention could be reversed.
"""
@syntax FreeCocartesianCategory(ObExpr,HomExpr) CocartesianCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  
  copair(f::Hom, g::Hom) = compose(otimes(f,g), mmerge(codom(f)))
  incl1(A::Ob, B::Ob) = otimes(id(A), create(B))
  incl2(A::Ob, B::Ob) = otimes(create(A), id(B))
end

function show_latex(io::IO, expr::HomExpr{:mmerge}; kw...)
  Syntax.show_latex_script(io, expr, "\\nabla")
end
function show_latex(io::IO, expr::HomExpr{:create}; kw...)
  Syntax.show_latex_script(io, expr, "\\square")
end

# Biproduct category
####################

""" Doctrine of *monoidal category with bidiagonals*

The terminology is nonstandard (is there any standard terminology?) but is
intended to mean a monoidal category with coherent diagonals and codiagonals.
Unlike in a biproduct category, the naturality axioms need not be satisfied.

FIXME: This signature should extend both `MonoidalCategoryWithDiagonals` and
`MonoidalCategoryWithCodiagonals`, but we don't support multiple inheritance.
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => MonoidalCategoryWithBidiagonals(Ob,Hom) begin
  mcopy(A::Ob)::Hom(A,otimes(A,A))
  mmerge(A::Ob)::Hom(otimes(A,A),A)
  delete(A::Ob)::Hom(A,munit())
  create(A::Ob)::Hom(munit(),A)
  
  # Unicode syntax
  ∇(A::Ob) = mmerge(A)
  Δ(A::Ob) = mcopy(A)
  ◇(A::Ob) = delete(A)
  □(A::Ob) = create(A)
end

""" Doctrine of *bicategory category*

Also known as a *semiadditive category*.

FIXME: This signature should extend `MonoidalCategoryWithBidiagonals`,
`CartesianCategory`, and `CocartesianCategory`, but we don't support multiple
inheritance.
"""
@signature MonoidalCategoryWithBidiagonals(Ob,Hom) => BiproductCategory(Ob,Hom) begin
  pair(f::Hom(A,B), g::Hom(A,C))::Hom(A,otimes(B,C)) <= (A::Ob, B::Ob, C::Ob)
  copair(f::Hom(A,C), g::Hom(B,C))::Hom(otimes(A,B),C) <= (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::Hom(otimes(A,B),A)
  proj2(A::Ob, B::Ob)::Hom(otimes(A,B),B)
  incl1(A::Ob, B::Ob)::Hom(A,otimes(A,B))
  incl2(A::Ob, B::Ob)::Hom(B,otimes(A,B))
end

@syntax FreeBiproductCategory(ObExpr,HomExpr) BiproductCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))

  pair(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g))
  copair(f::Hom, g::Hom) = compose(otimes(f,g), mmerge(codom(f)))
  proj1(A::Ob, B::Ob) = otimes(id(A), delete(B))
  proj2(A::Ob, B::Ob) = otimes(delete(A), id(B))
  incl1(A::Ob, B::Ob) = otimes(id(A), create(B))
  incl2(A::Ob, B::Ob) = otimes(create(A), id(B))
end

# Cartesian closed category
###########################

""" Doctrine of *cartesian closed category* (aka, CCC)

A CCC is a cartesian category with internal homs (aka, exponential objects).
"""
@signature CartesianCategory(Ob,Hom) => CartesianClosedCategory(Ob,Hom) begin
  # Internal hom of A and B, an object representing Hom(A,B)
  hom(A::Ob, B::Ob)::Ob
  
  # Evaluation map
  ev(A::Ob, B::Ob)::Hom(otimes(hom(A,B),A),B)
  
  # Currying (aka, lambda abstraction)
  curry(A::Ob, B::Ob, f::Hom(otimes(A,B),C))::Hom(A,hom(B,C)) <= (C::Ob)
end

""" Syntax for a free cartesian closed category.

See also `FreeCartesianCategory`.
"""
@syntax FreeCartesianClosedCategory(ObExpr,HomExpr) CartesianClosedCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  
  pair(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g))
  proj1(A::Ob, B::Ob) = otimes(id(A), delete(B))
  proj2(A::Ob, B::Ob) = otimes(delete(A), id(B))
end

function show_latex(io::IO, expr::ObExpr{:hom}; kw...)
  show_latex(io, last(expr))
  print(io, "^{")
  show_latex(io, first(expr))
  print(io, "}")
end
function show_latex(io::IO, expr::HomExpr{:ev}; kw...)
  Syntax.show_latex_script(io, expr, "\\mathrm{eval}")
end
function show_latex(io::IO, expr::HomExpr{:curry}; kw...)
  print(io, "\\lambda ")
  show_latex(io, last(expr))
end

# Compact closed category
#########################

""" Doctrine of *compact closed category*
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => CompactClosedCategory(Ob,Hom) begin
  # Dual A^* of object A
  dual(A::Ob)::Ob
  
  # Unit of duality, aka the coevaluation map
  dunit(A::Ob)::Hom(munit(), otimes(dual(A),A))
  
  # Counit of duality, aka the evaluation map
  dcounit(A::Ob)::Hom(otimes(A,dual(A)), munit())
  
  # Closed monoidal category
  hom(A::Ob, B::Ob) = otimes(B, dual(A))
  ev(A::Ob, B::Ob) = otimes(id(B), compose(braid(dual(A),A), dcounit(A)))
  curry(A::Ob, B::Ob, f::Hom) = compose(
    otimes(id(A), compose(dunit(B), braid(dual(B),B))),
    otimes(f, id(dual(B)))
  )
end

@syntax FreeCompactClosedCategory(ObExpr,HomExpr) CompactClosedCategory begin
  dual(A::Ob) = anti_involute(Super.dual(A), dual, otimes, munit)
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

function show_latex(io::IO, expr::ObExpr{:dual}; kw...)
  show_latex(io, first(expr))
  print(io, "^*")
end
function show_latex(io::IO, expr::HomExpr{:dunit}; kw...)
  Syntax.show_latex_script(io, expr, "\\eta")
end
function show_latex(io::IO, expr::HomExpr{:dcounit}; kw...)
  Syntax.show_latex_script(io, expr, "\\varepsilon")
end

# Dagger category
#################

""" Doctrine of *dagger category*
"""
@signature Category(Ob,Hom) => DaggerCategory(Ob,Hom) begin
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
end

@syntax FreeDaggerCategory(ObExpr,HomExpr) DaggerCategory begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  dagger(f::Hom) = anti_involute(Super.dagger(f), dagger, compose, id)
end

""" Doctrine of *dagger compact category*

FIXME: This signature should extend both `DaggerCategory` and
`CompactClosedCategory`, but we don't support multiple inheritance yet.
"""
@signature CompactClosedCategory(Ob,Hom) => DaggerCompactCategory(Ob,Hom) begin
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
end

@syntax FreeDaggerCompactCategory(ObExpr,HomExpr) DaggerCompactCategory begin
  dual(A::Ob) = anti_involute(Super.dual(A), dual, otimes, munit)
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  function dagger(f::Hom)
    f = anti_involute(Super.dagger(f), dagger, compose, id)
    distribute_unary(f, dagger, otimes)
  end
end

function show_latex(io::IO, expr::HomExpr{:dagger}; kw...)
  f = first(expr)
  if (head(f) != :generator) print(io, "\\left(") end
  show_latex(io, f)
  if (head(f) != :generator) print(io, "\\right)") end
  print(io, "^\\dagger")
end
