export MonoidalCategory, otimes, munit, ⊗, collect, ndims,
  SymmetricMonoidalCategory, FreeSymmetricMonoidalCategory, braid, σ,
  MonoidalCategoryWithDiagonals, CartesianCategory, FreeCartesianCategory,
  mcopy, delete, pair, proj1, proj2, Δ, ◊,
  mmerge, create, copair, incl1, incl2, ∇, □,
  MonoidalCategoryWithBidiagonals, BiproductCategory, FreeBiproductCategory,
  ClosedMonoidalCategory, FreeClosedMonoidalCategory, hom, ev, curry,
  CartesianClosedCategory, FreeCartesianClosedCategory,
  CompactClosedCategory, FreeCompactClosedCategory, dual, dunit, dcounit, mate,
  DaggerCategory, FreeDaggerCategory, dagger,
  DaggerSymmetricMonoidalCategory, FreeDaggerSymmetricMonoidalCategory,
  DaggerCompactCategory, FreeDaggerCompactCategory,
  TracedMonoidalCategory, FreeTracedMonoidalCategory, trace

import Base: collect, ndims

# Monoidal category
###################

""" Doctrine of *monoidal category*

To avoid associators and unitors, we assume the monoidal category is *strict*.
By the coherence theorem there is no loss of generality, but we may add a
theory for weak monoidal categories later.
"""
@signature Category(Ob,Hom) => MonoidalCategory(Ob,Hom) begin
  otimes(A::Ob, B::Ob)::Ob
  @op (⊗) := otimes
  otimes(f::(A → B), g::(C → D))::((A ⊗ C) → (B ⊗ D)) ⊣
    (A::Ob, B::Ob, C::Ob, D::Ob)
  munit()::Ob
end

# Convenience constructors
otimes(xs::Vector{T}) where T = isempty(xs) ? munit(T) : foldl(otimes, xs)
otimes(x, y, z, xs...) = otimes([x, y, z, xs...])

""" Collect generators of object in monoidal category as a vector.
"""
collect(expr::ObExpr) = [ expr ]
collect(expr::ObExpr{:otimes}) = vcat(map(collect, args(expr))...)
collect(expr::ObExpr{:munit}) = roottypeof(expr)[]

# XXX: We shouldn't have to do this.
roottype(T) = T isa UnionAll ? T : T.name.wrapper
roottypeof(x) = roottype(typeof(x))

""" Number of "dimensions" of object in monoidal category.
"""
ndims(expr::ObExpr) = 1
ndims(expr::ObExpr{:otimes}) = sum(map(ndims, args(expr)))
ndims(expr::ObExpr{:munit}) = 0

function show_unicode(io::IO, expr::Union{ObExpr{:otimes},HomExpr{:otimes}}; kw...)
  Syntax.show_unicode_infix(io, expr, "⊗"; kw...)
end
show_unicode(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

function show_latex(io::IO, expr::Union{ObExpr{:otimes},HomExpr{:otimes}}; kw...)
  Syntax.show_latex_infix(io, expr, "\\otimes"; kw...)
end
show_latex(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

# Symmetric monoidal category
#############################

""" Doctrine of *symmetric monoidal category*

The theory (but not the axioms) is the same as a braided monoidal category.
"""
@signature MonoidalCategory(Ob,Hom) => SymmetricMonoidalCategory(Ob,Hom) begin
  braid(A::Ob, B::Ob)::((A ⊗ B) → (B ⊗ A))
  @op (σ) := braid
end

@syntax FreeSymmetricMonoidalCategory(ObExpr,HomExpr) SymmetricMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
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
  mcopy(A::Ob)::(A → (A ⊗ A))
  @op (Δ) := mcopy
  delete(A::Ob)::(A → munit())
  @op (◊) := delete
end

""" Doctrine of *cartesian category*

Actually, this is a cartesian *symmetric monoidal* category but we omit these
qualifiers for brevity.
"""
@theory MonoidalCategoryWithDiagonals(Ob,Hom) => CartesianCategory(Ob,Hom) begin
  pair(f::(A → B), g::(A → C))::(A → (B ⊗ C)) ⊣ (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::((A ⊗ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊗ B) → B)

  pair(f, g) == Δ(A) ⋅ (f ⊗ g) ⊣ (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → C))
  proj1(A, B) == id(A) ⊗ ◊(B) ⊣ (A::Ob, B::Ob)
  proj2(A, B) == ◊(A) ⊗ id(B) ⊣ (A::Ob, B::Ob)
end

""" Syntax for a free cartesian category.

In this syntax, the pairing and projection operations are defined using
duplication and deletion, and do not have their own syntactic elements.
Of course, this convention could be reversed.
"""
@syntax FreeCartesianCategory(ObExpr,HomExpr) CartesianCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))

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

# Biproduct category
####################

""" Doctrine of *monoidal category with bidiagonals*

The terminology is nonstandard (is there any standard terminology?) but is
intended to mean a monoidal category with coherent diagonals and codiagonals.
Unlike in a biproduct category, the naturality axioms need not be satisfied.

FIXME: This theory should extend both `MonoidalCategoryWithDiagonals` and
`MonoidalCategoryWithCodiagonals`, but multiple inheritance is not yet
supported.
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => MonoidalCategoryWithBidiagonals(Ob,Hom) begin
  mcopy(A::Ob)::(A → (A ⊗ A))
  @op (Δ) := mcopy
  mmerge(A::Ob)::((A ⊗ A) → A)
  @op (∇) := mmerge
  delete(A::Ob)::(A → munit())
  @op (◊) := delete
  create(A::Ob)::(munit() → A)
  @op (□) := create
end

""" Doctrine of *bicategory category*

Also known as a *semiadditive category*.

FIXME: This theory should extend `MonoidalCategoryWithBidiagonals`,
`CartesianCategory`, and `CocartesianCategory`, but multiple inheritance is not
yet supported.
"""
@signature MonoidalCategoryWithBidiagonals(Ob,Hom) => BiproductCategory(Ob,Hom) begin
  pair(f::(A → B), g::(A → C))::(A → (B ⊗ C)) ⊣ (A::Ob, B::Ob, C::Ob)
  copair(f::(A → C), g::(B → C))::((A ⊗ B) → C) ⊣ (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::((A ⊗ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊗ B) → B)
  incl1(A::Ob, B::Ob)::(A → (A ⊗ B))
  incl2(A::Ob, B::Ob)::(B → (A ⊗ B))
end

@syntax FreeBiproductCategory(ObExpr,HomExpr) BiproductCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))

  pair(f::Hom, g::Hom) = Δ(dom(f)) → (f ⊗ g)
  copair(f::Hom, g::Hom) = (f ⊗ g) → ∇(codom(f))
  proj1(A::Ob, B::Ob) = id(A) ⊗ ◊(B)
  proj2(A::Ob, B::Ob) = ◊(A) ⊗ id(B)
  incl1(A::Ob, B::Ob) = id(A) ⊗ □(B)
  incl2(A::Ob, B::Ob) = □(A) ⊗ id(B)
end

# Closed monoidal category
##########################

""" Doctrine of *(symmetric) closed monoidal category*
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => ClosedMonoidalCategory(Ob,Hom) begin
  # Internal hom of A and B, an object representing Hom(A,B)
  hom(A::Ob, B::Ob)::Ob

  # Evaluation map
  ev(A::Ob, B::Ob)::((hom(A,B) ⊗ A) → B)

  # Currying (aka, lambda abstraction)
  curry(A::Ob, B::Ob, f::((A ⊗ B) → C))::(A → hom(B,C)) ⊣ (C::Ob)
end

""" Syntax for a free closed monoidal category.
"""
@syntax FreeClosedMonoidalCategory(ObExpr,HomExpr) ClosedMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end

function show_latex(io::IO, expr::ObExpr{:hom}; kw...)
  print(io, "{")
  show_latex(io, last(expr), paren=true)
  print(io, "}^{")
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

# Cartesian closed category
###########################

""" Doctrine of *cartesian closed category* (aka, CCC)

A CCC is a cartesian category with internal homs (aka, exponential objects).

FIXME: This theory should extend `ClosedMonoidalCategory`, but multiple
inheritance is not yet supported.
"""
@signature CartesianCategory(Ob,Hom) => CartesianClosedCategory(Ob,Hom) begin
  hom(A::Ob, B::Ob)::Ob
  ev(A::Ob, B::Ob)::((hom(A,B) ⊗ A) → B)
  curry(A::Ob, B::Ob, f::((A ⊗ B) → C))::(A → hom(B,C)) ⊣ (C::Ob)
end

""" Syntax for a free cartesian closed category.

See also `FreeCartesianCategory`.
"""
@syntax FreeCartesianClosedCategory(ObExpr,HomExpr) CartesianClosedCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))

  pair(f::Hom, g::Hom) = Δ(dom(f)) → (f ⊗ g)
  proj1(A::Ob, B::Ob) = id(A) ⊗ ◊(B)
  proj2(A::Ob, B::Ob) = ◊(A) ⊗ id(B)
end

# Compact closed category
#########################

""" Doctrine of *compact closed category*
"""
@theory ClosedMonoidalCategory(Ob,Hom) => CompactClosedCategory(Ob,Hom) begin
  # Dual A^* of object A
  dual(A::Ob)::Ob

  # Unit of duality, aka the coevaluation map
  dunit(A::Ob)::(munit() → (dual(A) ⊗ A))

  # Counit of duality, aka the evaluation map
  dcounit(A::Ob)::((A ⊗ dual(A)) → munit())

  # Adjoint mate of morphism f.
  mate(f::(A → B))::(dual(B) → dual(A)) ⊣ (A::Ob, B::Ob)
  
  # Axioms for closed monoidal structure.
  hom(A, B) == B ⊗ dual(A) ⊣ (A::Ob, B::Ob)
  ev(A, B) == id(B) ⊗ (σ(dual(A), A) ⋅ dcounit(A)) ⊣ (A::Ob, B::Ob)
  (curry(A, B, f) == (id(A) ⊗ (dunit(B) ⋅ σ(dual(B), B))) ⋅ (f ⊗ id(dual(B)))
   ⊣ (A::Ob, B::Ob, C::Ob, f::((A ⊗ B) → C)))
end

@syntax FreeCompactClosedCategory(ObExpr,HomExpr) CompactClosedCategory begin
  dual(A::Ob) = distribute_unary(involute(new(A)), dual, otimes,
                                 unit=munit, contravariant=true)
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  mate(f::Hom) = distribute_mate(involute(new(f)))
  hom(A::Ob, B::Ob) = B ⊗ dual(A)
  ev(A::Ob, B::Ob) = id(B) ⊗ (σ(dual(A), A) ⋅ dcounit(A))
  curry(A::Ob, B::Ob, f::Hom) =
    (id(A) ⊗ (dunit(B) ⋅ σ(dual(B), B))) ⋅ (f ⊗ id(dual(B)))
end

""" Distribute adjoint mates over composition and products.
"""
function distribute_mate(f::HomExpr)
  distribute_unary(
    distribute_unary(f, mate, compose, contravariant=true),
    mate, otimes, contravariant=true)
end

function show_latex(io::IO, expr::ObExpr{:dual}; kw...)
  Syntax.show_latex_postfix(io, expr, "^*")
end
function show_latex(io::IO, expr::HomExpr{:dunit}; kw...)
  Syntax.show_latex_script(io, expr, "\\eta")
end
function show_latex(io::IO, expr::HomExpr{:dcounit}; kw...)
  Syntax.show_latex_script(io, expr, "\\varepsilon")
end
function show_latex(io::IO, expr::HomExpr{:mate}; kw...)
  Syntax.show_latex_postfix(io, expr, "^*")
end

# Dagger category
#################

""" Doctrine of *dagger category*
"""
@signature Category(Ob,Hom) => DaggerCategory(Ob,Hom) begin
  dagger(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)
end

@syntax FreeDaggerCategory(ObExpr,HomExpr) DaggerCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  dagger(f::Hom) = distribute_dagger(involute(new(f)))
end

""" Distribute dagger over composition.
"""
function distribute_dagger(f::HomExpr)
  distribute_unary(f, dagger, compose, unit=id, contravariant=true)
end

""" Doctrine of *dagger symmetric monoidal category*

Also known as a [symmetric monoidal dagger
category](https://ncatlab.org/nlab/show/symmetric+monoidal+dagger-category).

FIXME: This theory should extend both `DaggerCategory` and
`SymmetricMonoidalCategory`, but multiple inheritance is not yet supported.
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => DaggerSymmetricMonoidalCategory(Ob,Hom) begin
  dagger(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)
end

@syntax FreeDaggerSymmetricMonoidalCategory(ObExpr,HomExpr) DaggerSymmetricMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
end

""" Doctrine of *dagger compact category*

In a dagger compact category, there are two kinds of adjoints of a morphism
`f::Hom(A,B)`, the adjoint mate `mate(f)::Hom(dual(B),dual(A))` and the dagger
adjoint `dagger(f)::Hom(B,A)`. In the category of Hilbert spaces, these are
respectively the Banach space adjoint and the Hilbert space adjoint (Reed-Simon,
Vol I, Sec VI.2). In Julia, they would correspond to `transpose` and `adjoint`
in the official `LinearAlegbra` module. For the general relationship between
mates and daggers, see Selinger's survey of graphical languages for monoidal
categories.

FIXME: This theory should extend both `DaggerCategory` and
`CompactClosedCategory`, but multiple inheritance is not yet supported.
"""
@signature CompactClosedCategory(Ob,Hom) => DaggerCompactCategory(Ob,Hom) begin
  dagger(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)
end

@syntax FreeDaggerCompactCategory(ObExpr,HomExpr) DaggerCompactCategory begin
  dual(A::Ob) = distribute_unary(involute(new(A)), dual, otimes,
                                 unit=munit, contravariant=true)
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
  mate(f::Hom) = distribute_mate(involute(new(f)))
end

function show_latex(io::IO, expr::HomExpr{:dagger}; kw...)
  Syntax.show_latex_postfix(io, expr, "^\\dagger")
end

# Traced monoidal category
##########################

""" Doctrine of *traced monoidal category*
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => TracedMonoidalCategory(Ob,Hom) begin
  trace(X::Ob, A::Ob, B::Ob, f::((X ⊗ A) → (X ⊗ B)))::(A → B)
end

@syntax FreeTracedMonoidalCategory(ObExpr,HomExpr) TracedMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  # FIXME: `GAT.equations` fails to identify the implicit equation.
  #trace(X::Ob, A::Ob, B::Ob, f::Hom) = new(X,A,B,f; strict=true)
end

function show_latex(io::IO, expr::HomExpr{:trace}; kw...)
  X, A, B, f = args(expr)
  print(io, "\\operatorname{Tr}_{$A,$B}^{$X} \\left($f\\right)")
end
