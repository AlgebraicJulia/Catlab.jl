module Doctrine
export
  Category, dom, codom, id, compose, ∘,
  MonoidalCategory, otimes, opow, munit, ⊗,
  SymmetricMonoidalCategory, braid, σ,
  InternalMonoid, InternalComonoid, mcopy, mmerge, create, delete, Δ, ∇,
  CompactClosedCategory, dual, ev, coev,
  DaggerCategory, dagger

using Typeclass

@doc """ Doctrine of *category* (with no extra structure)

**Warning**: We compose functions from left to right, i.e., if f:A→B and g:B→C
then compose(f,g):A→C. Under this convention function are applied on the right,
e.g., if a∈A then af∈B.

We retain the usual meaning of the symbol ∘, i.e., g∘f = compose(f,g).
This usage is too entrenched to overturn, however inconvenient it may be.
""" Category

@class Category Ob Mor begin
  dom(f::Mor)::Ob
  codom(f::Mor)::Ob
  id(A::Ob)::Mor
  compose(f::Mor, g::Mor)::Mor

  # Extra syntax
  compose(fs::Vararg{Mor}) = foldl(compose, fs)

  # Unicode syntax
  ∘(f::Mor, g::Mor) = compose(g, f)
  ∘(fs::Vararg{Mor}) = foldl(∘, fs)
end

@doc """ Doctrine of *monoidal category*

Parent typeclass: `Category`

To avoid associators and unitors, we assume the monoidal category is *strict*.
By the coherence theorem there is no loss of generality, but we may add a
typeclass for weak monoidal categories later.
""" MonoidalCategory

@class MonoidalCategory Ob Mor begin
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::Mor, g::Mor)::Mor
  munit(::Ob)::Ob

  # Extra syntax
  otimes(As::Vararg{Ob}) = foldl(otimes, As)
  otimes(fs::Vararg{Mor}) = foldl(otimes, fs)
  opow(A::Ob, n::Int) = otimes(repeated(A, n)...)
  opow(f::Mor, n::Int) = otimes(repeated(f, n)...)

  # Unicode syntax
  ⊗(A::Ob, B::Ob) = otimes(A, B)
  ⊗(f::Mor, g::Mor) = otimes(f, g)
  ⊗(As::Vararg{Ob}) = otimes(As...)
  ⊗(fs::Vararg{Mor}) = otimes(fs...)
end

@doc """ Doctrine of *symmetric monoidal category*

Parent typeclass: `MonoidalCategory`
""" SymmetricMonoidalCategory

@class SymmetricMonoidalCategory Ob Mor begin
  braid(A::Ob, B::Ob)::Mor
  
  # Unicode syntax
  σ(A::Ob, B::Ob) = braid(A, B)
end

@doc """ Doctrine of *monoidal category with internal monoid*

Parent typeclass: `MonoidalCategory`
""" InternalMonoid

@class InternalMonoid Ob Mor begin
  mmerge(A::Ob)::Mor  # A⊗A → A
  create(A::Ob)::Mor  # I → A
  
  # Unicode syntax
  ∇(A::Ob) = mmerge(A)
end

@doc """ Doctrine of *monoidal category with internal comonoid*

Parent typeclass: `MonoidalCategory`
""" InternalComonoid

@class InternalComonoid Ob Mor begin
  mcopy(A::Ob)::Mor  # A → A⊗A
  delete(A::Ob)::Mor # A → I
  
  # Unicode syntax
  Δ(A::Ob) = mcopy(A)
end

@doc """ Doctrine of *compact closed category*

Parent typeclass: `SymmetricMonoidalCategory`
""" CompactClosedCategory

@class CompactClosedCategory Ob Mor begin
  dual(A::Ob)::Ob  # A˟
  ev(A::Ob)::Mor   # A⊗A˟ → I
  coev(A::Ob)::Mor # I → A˟⊗A
end

@doc """ Doctrine of *dagger category*

Parent typeclass: `Category`
""" DaggerCategory

@class DaggerCategory Ob Mor begin
  dagger(f::Mor)::Mor
end

end
