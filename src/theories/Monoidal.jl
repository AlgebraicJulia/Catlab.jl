export ThMonoidalCategory, otimes, munit, ⊗, collect, ndims,
  ThSymmetricMonoidalCategory, FreeSymmetricMonoidalCategory, braid, σ,
  ThSymmetricMonoidalCopresheaf, elunit,
  ThMonoidalCategoryWithDiagonals, ThCartesianCategory, FreeCartesianCategory,
  mcopy, delete, pair, proj1, proj2, Δ, ◊,
  mmerge, create, copair, coproj1, coproj2, ∇, □,
  ThMonoidalCategoryWithBidiagonals, ThBiproductCategory, FreeBiproductCategory,
  ThClosedMonoidalCategory, FreeClosedMonoidalCategory, hom, ev, curry,
  ThCartesianClosedCategory, FreeCartesianClosedCategory,
  ThCompactClosedCategory, FreeCompactClosedCategory, dual, dunit, dcounit, mate,
  ThDaggerCategory, FreeDaggerCategory, dagger,
  ThDaggerSymmetricMonoidalCategory, FreeDaggerSymmetricMonoidalCategory,
  ThDaggerCompactCategory, FreeDaggerCompactCategory,
  ThTracedMonoidalCategory, FreeTracedMonoidalCategory, trace,
  ThHypergraphCategory, FreeHypergraphCategory


# Monoidal category
###################

""" Theory of *monoidal categories*

To avoid associators and unitors, we assume that the monoidal category is
*strict*. By the coherence theorem this involves no loss of generality, but we
might add a theory for weak monoidal categories later.
"""
@theory ThMonoidalCategory <: ThCategory begin
  @op (⊗) := otimes

  # Monoid operations.
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::(A → B), g::(C → D))::((A ⊗ C) → (B ⊗ D)) ⊣
    [A::Ob, B::Ob, C::Ob, D::Ob]
  munit()::Ob

  # Monoid axioms.
  #
  # The last two axioms are the naturality equations associated with the left
  # and right unitors, in the strict case where they are identities.
  (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C) ⊣ [A::Ob, B::Ob, C::Ob]
  munit() ⊗ A == A ⊣ [A::Ob]
  A ⊗ munit() == A ⊣ [A::Ob]
  (f ⊗ g) ⊗ h == f ⊗ (g ⊗ h) ⊣ [A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
                                f::(A → X), g::(B → Y), h::(C → Z)]
  id(munit()) ⊗ f == f ⊣ [A::Ob, B::Ob, f::(A → B)]
  f ⊗ id(munit()) == f ⊣ [A::Ob, B::Ob, f::(A → B)]

  # Functorality axioms.
  ((f ⊗ g) ⋅ (h ⊗ k) == (f ⋅ h) ⊗ (g ⋅ k)
    ⊣ [A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
       f::(A → B), h::(B → C), g::(X → Y), k::(Y → Z)])
  id(A ⊗ B) == id(A) ⊗ id(B) ⊣ [A::Ob, B::Ob]
end

# Convenience constructors
otimes(xs::AbstractVector{T})where {T} = #{T<:GATExpr} =
  isempty(xs) ? munit(T) : foldl(otimes, xs)
  
otimes(x::GATExpr, y::GATExpr, z::GATExpr, xs...) = 
  otimes(GATExpr[x, y, z, xs...])

""" Collect generators of object in monoidal category as a vector.
"""
collect(expr::ObExpr) = [ expr ]
collect(expr::ObExpr{:otimes}) = vcat(map(collect, args(expr))...)
collect(expr::E) where E <: ObExpr{:munit} = Base.typename(E).wrapper[]

""" Number of "dimensions" of object in monoidal category.
"""
ndims(expr::ObExpr) = 1
ndims(expr::ObExpr{:otimes}) = sum(map(ndims, args(expr)))
ndims(expr::ObExpr{:munit}) = 0

show_unicode(io::IO, expr::CategoryExpr{:otimes}; kw...) =
  show_unicode_infix(io, expr, "⊗"; kw...)
show_unicode(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

show_latex(io::IO, expr::CategoryExpr{:otimes}; kw...) =
  show_latex_infix(io, expr, "\\otimes"; kw...)
show_latex(io::IO, expr::ObExpr{:munit}; kw...) = print(io, "I")

# Symmetric monoidal category
#############################

""" Theory of (strict) *symmetric monoidal categories*
"""
@theory ThSymmetricMonoidalCategory <: ThMonoidalCategory begin
  braid(A::Ob, B::Ob)::((A ⊗ B) → (B ⊗ A))
  @op (σ) := braid

  # Involutivity axiom.
  σ(A,B) ⋅ σ(B,A) == id(A ⊗ B) ⊣ [A::Ob, B::Ob]

  # Coherence axioms.
  #
  # Note: The last two axioms are deducible from the first two axioms together
  # with the naturality equations for the left/right unitors. We record them for
  # the sake of clarity and uniformity.
  σ(A,B⊗C) == (σ(A,B) ⊗ id(C)) ⋅ (id(B) ⊗ σ(A,C)) ⊣ [A::Ob, B::Ob, C::Ob]
  σ(A⊗B,C) == (id(A) ⊗ σ(B,C)) ⋅ (σ(A,C) ⊗ id(B)) ⊣ [A::Ob, B::Ob, C::Ob]
  σ(A,munit()) == id(A) ⊣ [A::Ob]
  σ(munit(),A) == id(A) ⊣ [A::Ob]

  # Naturality axiom.
  (f ⊗ g) ⋅ σ(B,D) == σ(A,C) ⋅ (g ⊗ f) ⊣ [A::Ob, B::Ob, C::Ob, D::Ob,
                                          f::(A → B), g::(C → D)]
end

@symbolic_model FreeSymmetricMonoidalCategory{ObExpr,HomExpr} ThSymmetricMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

show_unicode(io::IO, expr::CategoryExpr{:braid}; kw...) =
  show_unicode_infix(io, expr, "σ"; kw...)
show_latex(io::IO, expr::CategoryExpr{:braid}; kw...) =
  show_latex_script(io, expr, "\\sigma")

""" Theory of a *symmetric monoidal copresheaf*

The name is not standard but refers to a lax symmetric monoidal functor into
**Set**. This can be interpreted as an action of a symmetric monoidal category,
just as a copresheaf (set-valued functor) is an action of a category. The theory
is simpler than that of a general lax monoidal functor because (1) the domain is
a strict monoidal category and (2) the codomain is fixed to the cartesian
monoidal category **Set**.

FIXME: This theory should also extend `ThCopresheaf` but multiple inheritance is
not yet supported.
"""
@theory ThSymmetricMonoidalCopresheaf <: ThSymmetricMonoidalCategory begin
  El(ob::Ob)::TYPE

  # Functor.
  act(x::El(A), f::Hom(A,B))::El(B) ⊣ [A::Ob, B::Ob]
  # @op (⋅) := act

  # Laxator.
  otimes(x::El(A), y::El(B))::El(otimes(A,B)) ⊣ [A::Ob, B::Ob]
  elunit()::El(munit())

  # Functorality axioms.
  act(act(x, f), g) == act(x, (f ⋅ g)) ⊣
    [A::Ob, B::Ob, C::Ob, f::(A → B), g::(B → C), x::El(A)]
  # x ⋅ id(A) == x ⊣ [A::Ob, x::El(A)]

  # Naturality of laxator.
  # (x ⊗ y), (f ⊗ g) == (x ⋅ f) ⊗ (y ⋅ g) ⊣
  #   [A::Ob, B::Ob, C::Ob, D::Ob, x::El(A), y::El(B), f::(A → C), g::(B → D)]

  # # Commutative monoid axioms for laxator.
  # (x ⊗ y) ⊗ z == x ⊗ (y ⊗ z) ⊣
  #   [A::Ob, B::Ob, C::Ob, x::El(A), y::El(B), z::El(C)]
  # x ⊗ elunit() == x ⊣ [A::Ob, x::El(A)]
  # elunit() ⊗ x == x ⊣ [A::Ob, x::El(A)]
  # (x ⊗ y) ⋅ σ(A,B) == y ⊗ x ⊣ [A::Ob, B::Ob, x::El(A), y::El(B)]
end

# Cartesian category
####################

""" Theory of *monoidal categories with diagonals*

A monoidal category with diagonals is a symmetric monoidal category equipped
with coherent operations of copying and deleting, also known as a supply of
commutative comonoids. Unlike in a cartesian category, the naturality axioms
need not be satisfied.

References:

- Fong & Spivak, 2019, "Supplying bells and whistles in symmetric monoidal
  categories" ([arxiv:1908.02633](https://arxiv.org/abs/1908.02633))
- Selinger, 2010, "A survey of graphical languages for monoidal categories",
  Section 6.6: "Cartesian center"
- Selinger, 1999, "Categorical structure of asynchrony"
"""
@theory ThMonoidalCategoryWithDiagonals <: ThSymmetricMonoidalCategory begin
  mcopy(A::Ob)::(A → (A ⊗ A))
  @op (Δ) := mcopy
  delete(A::Ob)::(A → munit())
  @op (◊) := delete

  # Commutative comonoid axioms.
  Δ(A) ⋅ (Δ(A) ⊗ id(A)) == Δ(A) ⋅ (id(A) ⊗ Δ(A)) ⊣ [A::Ob]
  Δ(A) ⋅ (◊(A) ⊗ id(A)) == id(A) ⊣ [A::Ob]
  Δ(A) ⋅ (id(A) ⊗ ◊(A)) == id(A) ⊣ [A::Ob]
  Δ(A) ⋅ σ(A,A) == Δ(A) ⊣ [A::Ob]

  # Coherence axioms.
  Δ(A⊗B) == (Δ(A) ⊗ Δ(B)) ⋅ (id(A) ⊗ σ(A,B) ⊗ id(B)) ⊣ [A::Ob, B::Ob]
  ◊(A⊗B) == ◊(A) ⊗ ◊(B) ⊣ [A::Ob, B::Ob]
  Δ(munit()) == id(munit())
  ◊(munit()) == id(munit())
end

""" Theory of *cartesian (monoidal) categories*

For the traditional axiomatization of products, see
[`ThCategoryWithProducts`](@ref).
"""
@theory ThCartesianCategory <: ThMonoidalCategoryWithDiagonals begin
  pair(f::(A → B), g::(A → C))::(A → (B ⊗ C)) ⊣ [A::Ob, B::Ob, C::Ob]
  proj1(A::Ob, B::Ob)::((A ⊗ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊗ B) → B)

  # Definitions of pairing and projections.
  pair(f,g) == Δ(C)⋅(f⊗g) ⊣ [A::Ob, B::Ob, C::Ob, f::(C → A), g::(C → B)]
  proj1(A,B) == id(A)⊗◊(B) ⊣ [A::Ob, B::Ob]
  proj2(A,B) == ◊(A)⊗id(B) ⊣ [A::Ob, B::Ob]
  
  # Naturality axioms.
  f⋅Δ(B) == Δ(A)⋅(f⊗f) ⊣ [A::Ob, B::Ob, f::(A → B)]
  f⋅◊(B) == ◊(A) ⊣ [A::Ob, B::Ob, f::(A → B)]
end

""" Syntax for a free cartesian category.

In this syntax, the pairing and projection operations are defined using
duplication and deletion, and do not have their own syntactic elements.
This convention could be dropped or reversed.
"""
@symbolic_model FreeCartesianCategory{ObExpr,HomExpr} ThCartesianCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)

  pair(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g))
  proj1(A::Ob, B::Ob) = otimes(id(A), delete(B))
  proj2(A::Ob, B::Ob) = otimes(delete(A), id(B))
end

show_latex(io::IO, expr::HomExpr{:mcopy}; kw...) =
  show_latex_script(io, expr, "\\Delta")
show_latex(io::IO, expr::HomExpr{:delete}; kw...) =
  show_latex_script(io, expr, "\\lozenge")

# Biproduct category
####################

""" Theory of *monoidal categories with bidiagonals*

The terminology is nonstandard (is there any standard terminology?) but is
supposed to mean a monoidal category with coherent diagonals and codiagonals.
Unlike in a biproduct category, the naturality axioms need not be satisfied.
"""
@signature ThMonoidalCategoryWithBidiagonals <:
    ThMonoidalCategoryWithDiagonals begin
  mmerge(A::Ob)::((A ⊗ A) → A)
  @op (∇) := mmerge
  create(A::Ob)::(munit() → A)
  @op (□) := create
end

""" Theory of *biproduct categories*

Mathematically the same as [`ThSemiadditiveCategory`](@ref) but written
multiplicatively, instead of additively.
"""
@theory ThBiproductCategory <: ThMonoidalCategoryWithBidiagonals begin
  pair(f::(A → B), g::(A → C))::(A → (B ⊗ C)) ⊣ [A::Ob, B::Ob, C::Ob]
  copair(f::(A → C), g::(B → C))::((A ⊗ B) → C) ⊣ [A::Ob, B::Ob, C::Ob]
  proj1(A::Ob, B::Ob)::((A ⊗ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊗ B) → B)
  coproj1(A::Ob, B::Ob)::(A → (A ⊗ B))
  coproj2(A::Ob, B::Ob)::(B → (A ⊗ B))
  
  # Naturality axioms.
  f⋅Δ(B) == Δ(A)⋅(f⊗f) ⊣ [A::Ob, B::Ob, f::(A → B)]
  f⋅◊(B) == ◊(A) ⊣ [A::Ob, B::Ob, f::(A → B)]
  ∇(A)⋅f == (f⊗f)⋅∇(B) ⊣ [A::Ob, B::Ob, f::(A → B)]
  □(A)⋅f == □(B) ⊣ [A::Ob, B::Ob, f::(A → B)]
  
  # Bimonoid axioms. (These follow from naturality + coherence axioms.)
  ∇(A)⋅Δ(A) == (Δ(A)⊗Δ(A)) ⋅ (id(A)⊗σ(A,A)⊗id(A)) ⋅ (∇(A)⊗∇(A)) ⊣ [A::Ob]
  ∇(A)⋅◊(A) == ◊(A) ⊗ ◊(A) ⊣ [A::Ob]
  □(A)⋅Δ(A) == □(A) ⊗ □(A) ⊣ [A::Ob]
  □(A)⋅◊(A) == id(munit()) ⊣ [A::Ob]
end

@symbolic_model FreeBiproductCategory{ObExpr,HomExpr} ThBiproductCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)

  pair(f::Hom, g::Hom) = Δ(dom(f)) ⋅ (f ⊗ g)
  copair(f::Hom, g::Hom) = (f ⊗ g) ⋅ ∇(codom(f))
  proj1(A::Ob, B::Ob) = id(A) ⊗ ◊(B)
  proj2(A::Ob, B::Ob) = ◊(A) ⊗ id(B)
  coproj1(A::Ob, B::Ob) = id(A) ⊗ □(B)
  coproj2(A::Ob, B::Ob) = □(A) ⊗ id(B)
end

show_latex(io::IO, expr::HomExpr{:mmerge}; kw...) =
  show_latex_script(io, expr, "\\nabla")
show_latex(io::IO, expr::HomExpr{:create}; kw...) =
  show_latex_script(io, expr, "\\square")

# Closed monoidal category
##########################

""" Theory of (symmetric) *closed monoidal categories*
"""
@signature ThClosedMonoidalCategory <: ThSymmetricMonoidalCategory begin
  # Internal hom of A and B, an object representing Hom(A,B)
  hom(A::Ob, B::Ob)::Ob

  # Evaluation map
  ev(A::Ob, B::Ob)::((hom(A,B) ⊗ A) → B)

  # Currying (aka, lambda abstraction)
  curry(A::Ob, B::Ob, f::((A ⊗ B) → C))::(A → hom(B,C)) ⊣ [C::Ob]
end

""" Syntax for a free closed monoidal category.
"""
@symbolic_model FreeClosedMonoidalCategory{ObExpr,HomExpr} ThClosedMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

function show_latex(io::IO, expr::ObExpr{:hom}; kw...)
  print(io, "{")
  show_latex(io, last(expr), paren=true)
  print(io, "}^{")
  show_latex(io, first(expr))
  print(io, "}")
end
function show_latex(io::IO, expr::HomExpr{:ev}; kw...)
  show_latex_script(io, expr, "\\mathrm{eval}")
end
function show_latex(io::IO, expr::HomExpr{:curry}; kw...)
  print(io, "\\lambda ")
  show_latex(io, last(expr))
end

# Cartesian closed category
###########################

""" Theory of *cartesian closed categories*, aka CCCs

A CCC is a cartesian category with internal homs (aka, exponential objects).

FIXME: This theory should also extend `ThClosedMonoidalCategory`, but multiple
inheritance is not yet supported.
"""
@signature ThCartesianClosedCategory <: ThCartesianCategory begin
  hom(A::Ob, B::Ob)::Ob
  ev(A::Ob, B::Ob)::((hom(A,B) ⊗ A) → B)
  curry(A::Ob, B::Ob, f::((A ⊗ B) → C))::(A → hom(B,C)) ⊣ [C::Ob]
end

""" Syntax for a free cartesian closed category.

See also `FreeCartesianCategory`.
"""
@symbolic_model FreeCartesianClosedCategory{ObExpr,HomExpr} ThCartesianClosedCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)

  pair(f::Hom, g::Hom) = Δ(dom(f)) ⋅ (f ⊗ g)
  proj1(A::Ob, B::Ob) = id(A) ⊗ ◊(B)
  proj2(A::Ob, B::Ob) = ◊(A) ⊗ id(B)
end

# Compact closed category
#########################

""" Theory of *compact closed categories*
"""
@theory ThCompactClosedCategory <: ThClosedMonoidalCategory begin
  # Dual A^* of object A
  dual(A::Ob)::Ob

  # Unit of duality, aka the coevaluation map
  dunit(A::Ob)::(munit() → (dual(A) ⊗ A))

  # Counit of duality, aka the evaluation map
  dcounit(A::Ob)::((A ⊗ dual(A)) → munit())

  # Adjoint mate of morphism f.
  mate(f::(A → B))::(dual(B) → dual(A)) ⊣ [A::Ob, B::Ob]
  
  # Axioms for closed monoidal structure.
  hom(A, B) == B ⊗ dual(A) ⊣ [A::Ob, B::Ob]
  ev(A, B) == id(B) ⊗ (σ(dual(A), A) ⋅ dcounit(A)) ⊣ [A::Ob, B::Ob]
  (curry(A, B, f) == (id(A) ⊗ (dunit(B) ⋅ σ(dual(B), B))) ⋅ (f ⊗ id(dual(B)))
   ⊣ [A::Ob, B::Ob, C::Ob, f::((A ⊗ B) → C)])
end

@symbolic_model FreeCompactClosedCategory{ObExpr,HomExpr} ThCompactClosedCategory begin
  dual(A::Ob) = distribute_unary(involute(new(A)), dual, otimes,
                                 unit=munit, contravariant=true)
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
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

show_latex(io::IO, expr::ObExpr{:dual}; kw...) =
  show_latex_postfix(io, expr, "^*")
show_latex(io::IO, expr::HomExpr{:dunit}; kw...) =
  show_latex_script(io, expr, "\\eta")
show_latex(io::IO, expr::HomExpr{:dcounit}; kw...) =
  show_latex_script(io, expr, "\\varepsilon")
show_latex(io::IO, expr::HomExpr{:mate}; kw...) =
  show_latex_postfix(io, expr, "^*")

# Dagger category
#################

""" Theory of *dagger categories*
"""
@signature ThDaggerCategory <: ThCategory begin
  dagger(f::(A → B))::(B → A) ⊣ [A::Ob, B::Ob]
end

@symbolic_model FreeDaggerCategory{ObExpr,HomExpr} ThDaggerCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  dagger(f::Hom) = distribute_dagger(involute(new(f)))
end

""" Distribute dagger over composition.
"""
function distribute_dagger(f::HomExpr)
  distribute_unary(f, dagger, compose, unit=id, contravariant=true)
end

""" Theory of *dagger symmetric monoidal categories*

Also known as a [symmetric monoidal dagger
category](https://ncatlab.org/nlab/show/symmetric+monoidal+dagger-category).

FIXME: This theory should also extend `ThDaggerCategory`, but multiple
inheritance is not yet supported.
"""
@signature ThDaggerSymmetricMonoidalCategory <: ThSymmetricMonoidalCategory begin
  dagger(f::(A → B))::(B → A) ⊣ [A::Ob, B::Ob]
end

@symbolic_model FreeDaggerSymmetricMonoidalCategory{ObExpr,HomExpr} ThDaggerSymmetricMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
end

""" Theory of *dagger compact categories*

In a dagger compact category, there are two kinds of adjoints of a morphism
`f::Hom(A,B)`, the adjoint mate `mate(f)::Hom(dual(B),dual(A))` and the dagger
adjoint `dagger(f)::Hom(B,A)`. In the category of Hilbert spaces, these are
respectively the Banach space adjoint and the Hilbert space adjoint (Reed-Simon,
Vol I, Sec VI.2). In Julia, they would correspond to `transpose` and `adjoint`
in the official `LinearAlegbra` module. For the general relationship between
mates and daggers, see Selinger's survey of graphical languages for monoidal
categories.

FIXME: This theory should also extend `ThDaggerCategory`, but multiple
inheritance is not yet supported.
"""
@signature ThDaggerCompactCategory <: ThCompactClosedCategory begin
  dagger(f::(A → B))::(B → A) ⊣ [A::Ob, B::Ob]
end

@symbolic_model FreeDaggerCompactCategory{ObExpr,HomExpr} ThDaggerCompactCategory begin
  dual(A::Ob) = distribute_unary(involute(new(A)), dual, otimes,
                                 unit=munit, contravariant=true)
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
  mate(f::Hom) = distribute_mate(involute(new(f)))
end

show_latex(io::IO, expr::HomExpr{:dagger}; kw...) =
  show_latex_postfix(io, expr, "^\\dagger")

# Traced monoidal category
##########################

""" Theory of *traced monoidal categories*
"""
@signature ThTracedMonoidalCategory <: ThSymmetricMonoidalCategory begin
  trace(X::Ob, A::Ob, B::Ob, f::((X ⊗ A) → (X ⊗ B)))::(A → B)
end

@symbolic_model FreeTracedMonoidalCategory{ObExpr,HomExpr} ThTracedMonoidalCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  # FIXME: `GAT.equations` fails to identify the implicit equation.
  #trace(X::Ob, A::Ob, B::Ob, f::Hom) = new(X,A,B,f; strict=true)
end

function show_latex(io::IO, expr::HomExpr{:trace}; kw...)
  X, A, B, f = args(expr)
  print(io, "\\operatorname{Tr}_{$A,$B}^{$X} \\left($f\\right)")
end

# Hypergraph category
#####################

""" Theory of *hypergraph categories*

Hypergraph categories are also known as "well-supported compact closed
categories" and "spidered/dungeon categories", among other things.

FIXME: Should also inherit `ThClosedMonoidalCategory` and `ThDaggerCategory`,
but multiple inheritance is not yet supported.
"""
@theory ThHypergraphCategory <: ThMonoidalCategoryWithBidiagonals begin
  # Self-dual compact closed category.
  dunit(A::Ob)::(munit() → (A ⊗ A))
  dcounit(A::Ob)::((A ⊗ A) → munit())
  dagger(f::(A → B))::(B → A) ⊣ [A::Ob, B::Ob]

  dunit(A) == create(A) ⋅ mcopy(A) ⊣ [A::Ob]
  dcounit(A) == mmerge(A) ⋅ delete(A) ⊣ [A::Ob]
  (dagger(f) == ((id(B) ⊗ dunit(A)) ⋅ (id(B) ⊗ f ⊗ id(A)) ⋅ (dcounit(B) ⊗ id(A)))
   ⊣ [A::Ob, B::Ob, f::(A → B)])
end

@symbolic_model FreeHypergraphCategory{ObExpr,HomExpr} ThHypergraphCategory begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  dagger(f::Hom) = distribute_unary(distribute_dagger(involute(new(f))),
                                    dagger, otimes)
end
