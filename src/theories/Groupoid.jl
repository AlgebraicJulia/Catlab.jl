export ThGroupoid, FreeGroupoid, inv

import Base: inv

# Groupoid
##########

""" Theory of *groupoids*.
"""
@theory ThGroupoid{Ob,Hom} <: ThCategory{Ob,Hom} begin
  inv(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)

  f ⋅ inv(f) == id(A) ⊣ (A::Ob, B::Ob, f::(A → B))
  inv(f) ⋅ f == id(B) ⊣ (A::Ob, B::Ob, f::(A → B))
end

@syntax FreeGroupoid{ObExpr,HomExpr} ThGroupoid begin
  compose(f::Hom, g::Hom) = associate_unit_inv(new(f,g; strict=true), id, inv)
  inv(f::Hom) = distribute_unary(involute(new(f)), inv, compose,
                                 unit=id, contravariant=true)
end
