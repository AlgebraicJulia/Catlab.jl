module Doctrine
export
  Category, dom, codom, id, compose, ∘,
  MonoidalCategory, otimes, munit, ⊗

using Typeclass

@doc """ Doctrine: *category* (with no extra structure)

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

@doc """ Doctrine: *monoidal category*

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

  # Unicode syntax
  ⊗(A::Ob, B::Ob) = otimes(A, B)
  ⊗(f::Mor, g::Mor) = otimes(f, g)
  ⊗(As::Vararg{Ob}) = otimes(As...)
  ⊗(fs::Vararg{Mor}) = otimes(fs...)
end

end
