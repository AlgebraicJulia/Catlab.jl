using Test
using Catlab
using Catlab.Doctrines

x,y,z = Ob(FreeThinCategory, :x, :y, :z)
f, g = Hom(:f, x, y), Hom(:g, y, z)
@test dom(compose(f,g)) == x
@test codom(compose(f,g)) == z


x,y,z = Ob(FreePreorder, :x, :y, :z)
@test_throws UndefVarError f, g = Leq(:f, x, y), Leq(:g, y, z)
# Preorder doesn't have domain and codomain defined.
@test_throws UndefVarError dom(transitive(f,g)) == x
@test_throws UndefVarError codom(transitive(f,g)) == z

x,y,z,zz = Ob(FreeMonoidalThinCategory, :x, :y, :z, :zz)
f, g, h= Hom(:f, x, y), Hom(:g, y, z), Hom(:h, otimes(y,y), z)
j = Hom(:j, y⊗z, zz)
@test dom(compose(f,g)) == x
@test codom(compose(f,g)) == z
@test dom(otimes(f,g)) == otimes(x,y)
@test codom(otimes(f,g)) == otimes(y,z)
@test dom((f⊗id(y))⋅h) == x⊗y
@test codom((f⊗id(y))⋅h) == z
@test dom((f⊗g)⋅j) == x⊗y
@test codom((f⊗g)⋅j) == zz


# # This should work, but doesn't
# @theory Preorder(Elt,Leq) begin
#   # METATYPES of the GAT
#   Elt::TYPE
#   Leq(lhs::Elt, rhs::Elt)::TYPE
#   @op (≤) := Leq
#   # Axioms of the mathematical object are lifted to term constructors in the GAT
#   reflexive(A::Elt)::(A≤A) # ∀ A there is a term reflexive(A) which implies A≤A
#   transitive(f::(A≤B), g::(B≤C))::(A≤C) ⊣ (A::Elt, B::Elt, C::Elt)
#
#   # axioms of the GAT are equivalences on terms or simplification rules in the logic
#   f == g ⊣ (A::Ob, B::Ob, f::(A≤B), g::(A≤B))
#   # read as (f⟹ A≤B ∧ g⟹ A≤B) ⟹ f ≡ g
# end
#
# @syntax FreePreorder(ObExpr,HomExpr) Preorder begin
#   transitive(f::Leq, g::Leq) = associate(new(f,g; strict=true))
# end
#
# x,y,z = Elt(FreePreorder, [:x, :y, :z])
# f, g = Leq(:f, x, y), Leq(:g, y, z)
#
# @show transitive(f,g)
