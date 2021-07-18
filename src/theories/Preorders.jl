export ThinCategory, FreeThinCategory,
  ThinSymmetricMonoidalCategory, FreeThinSymmetricMonoidalCategory,
  Preorder, FreePreorder, El, Leq, ≤, lhs, rhs, reflexive, transitive,
  Poset, Lattice, meet, ∧, join, ∨, top, ⊤, bottom, ⊥

# Thin category
###############

""" Theory of *thin categories*

Thin categories have at most one morphism between any two objects and are
isomorphic to preorders.
"""
@theory ThinCategory{Ob,Hom} <: Category{Ob,Hom} begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B))
end

@syntax FreeThinCategory{ObExpr,HomExpr} ThinCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
end

""" Theory of *thin symmetric monoidal category*

Thin SMCs are isomorphic to commutative monoidal prosets.
"""
@theory ThinSymmetricMonoidalCategory{Ob,Hom} <: SymmetricMonoidalCategory{Ob,Hom} begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B))
end

@syntax FreeThinSymmetricMonoidalCategory{ObExpr,HomExpr} ThinSymmetricMonoidalCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
end

# Preorder
##########

""" Theory of *preorders*

The generalized algebraic theory of preorders encodes inequalities ``A≤B`` as
dependent types ```Leq(A,B)`` and the axioms of reflexivity and transitivity as
term constructors.
"""
@theory Preorder{El,Leq} begin
  El::TYPE
  Leq(lhs::El, rhs::El)::TYPE
  @op (≤) := Leq

  reflexive(A::El)::(A≤A)
  transitive(f::(A≤B), g::(B≤C))::(A≤C) ⊣ (A::El, B::El, C::El)

  f == g ⊣ (A::El, B::El, f::(A≤B), g::(A≤B))
end

@syntax FreePreorder{ObExpr,HomExpr} Preorder begin
  transitive(f::Leq, g::Leq) = associate(new(f,g; strict=true))
end

# TODO: There should be an isomorphism in the category GAT between the theories
# of preorders and thin categories.
#
# @functor F(Preorder(El, Leq))::ThinCategory(Ob, Hom) begin
#   El ↦ Ob
#   Leq ↦ Hom
#   reflexive ↦ id
#   transitive ↦ compose
# end

""" Theory of *partial orders* (posets)
"""
@theory Poset{El,Leq} <: Preorder{El,Leq} begin
  A == B ⊣ (A::El, B::El, f::(A≤B), g::(B≤A))
end

# Lattice
#########

""" Theory of (bounded) *lattices*

A lattice is a poset with all finite meets and joins. Viewed as thin category,
this means that the category has all finite products and coproducts, hence the
names for the inequality constructors in the theory.
"""
@theory Lattice{El,Leq} <: Poset{El,Leq} begin
  @op begin
    (∧) := meet
    (⊤) := top
    (∨) := join
    (⊥) := bottom
  end

  # Meet = greatest lower bound.
  meet(A::El, B::El)::El
  proj1(A::El, B::El)::((A ∧ B) ≤ A)
  proj2(A::El, B::El)::((A ∧ B) ≤ B)
  pair(f::(C ≤ A), g::(C ≤ B))::(C ≤ (A ∧ B)) ⊣ (A::El, B::El, C::El)

  # Top = maximum.
  top()::El
  delete(A::El)::(A ≤ ⊤())

  # Join = least upper bound.
  join(A::El, B::El)::El
  coproj1(A::El, B::El)::(A ≤ (A ∨ B))
  coproj2(A::El, B::El)::(B ≤ (A ∨ B))
  copair(f::(A ≤ C), g::(B ≤ C))::((A ∨ B) ≤ C) ⊣ (A::El, B::El, C::El)

  # Bottom = minimum.
  bottom()::El
  create(A::El)::(⊥() ≤ A)
end
