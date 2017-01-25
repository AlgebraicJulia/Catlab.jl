module Doctrine
export Category, dom, codom, id, compose, ∘
export MonoidalCategory, otimes, munit, ⊗

using Typeclass

@class Category Ob Mor begin
  dom(f::Mor)::Ob
  codom(f::Mor)::Ob
  id(A::Ob)::Mor
  compose(f::Mor, g::Mor)::Mor

  # Unicode syntax
  ∘(f::Mor, g::Mor) = compose(f, g)
end

# Parent class: Category
@class MonoidalCategory Ob Mor begin
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::Mor, g::Mor)::Mor
  munit(::Ob)::Ob
  
  # Unicode syntax
  ⊗(A::Ob, B::Ob) = otimes(A, B)
  ⊗(f::Mor, g::Mor) = otimes(f, g)
end

end
