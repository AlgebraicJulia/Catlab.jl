export ThinCategory,
  FreeThinCategory,
  ThinSymmetricMonoidalCategory,
  FreeThinSymmetricMonoidalCategory,
  Preorder,
  FreePreorder,
  El,
  Leq,
  ≤,
  lhs,
  rhs,
  reflexive,
  transitive

# Thin category
###############

""" Theory of *thin categories*

Thin categories have at most one morphism between any two objects.
"""
@theory ThinCategory{Ob,Hom} <: Category{Ob,Hom} begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A, B), g::Hom(A, B))
end

@syntax FreeThinCategory{ObExpr,HomExpr} ThinCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f, g; strict=true), id)
end

@theory ThinSymmetricMonoidalCategory{Ob,Hom} <:
        SymmetricMonoidalCategory{Ob,Hom} begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A, B), g::Hom(A, B))
end

@syntax FreeThinSymmetricMonoidalCategory{ObExpr,HomExpr} ThinSymmetricMonoidalCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f, g; strict=true), id)
  otimes(A::Ob, B::Ob) = associate_unit(new(A, B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f, g))
end

# Preorder
##########

""" Theory of *preorders*

Preorders encode the axioms of reflexivity and transitivity as term constructors.
"""
@theory Preorder{El,Leq} begin
  El::TYPE
  Leq(lhs::El, rhs::El)::TYPE
  @op (≤) := Leq

  # Preorder axioms are lifted to term constructors in the GAT.
  reflexive(A::El)::(A ≤ A) # ∀ A there is a term reflexive(A) which implies A≤A
  transitive(f::(A ≤ B), g::(B ≤ C))::(A ≤ C) ⊣ (A::El, B::El, C::El)

  # Axioms of the GAT are equivalences on terms or simplification rules in the logic
  f == g ⊣ (A::El, B::El, f::(A ≤ B), g::(A ≤ B))
  # Read as (f⟹ A≤B ∧ g⟹ A≤B) ⟹ f ≡ g
end

@syntax FreePreorder{ObExpr,HomExpr} Preorder begin
  transitive(f::Leq, g::Leq) = associate(new(f, g; strict=true))
end

# TODO: a GAT-homomorphism between the Preorder GAT and the ThinCategory GAT
# this is a morphism is *GAT* the category whose objects are GATs
# and whose morphisms are algebraic structure preserving maps

# @functor F(Preorder(El, Leq))::ThinCategory(Ob, Hom) begin
#   El ↦ Ob
#   Leq ↦ Hom
#   reflexive ↦ id
#   transitive ↦ compose
# end
