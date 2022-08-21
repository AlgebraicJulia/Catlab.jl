export ThGroupoid, FreeGroupoid, inverse

# Groupoid
##########

""" Theory of *groupoids*.
"""

@theory ThGroupoid{Ob,Hom} <: ThCategory{Ob,Hom} begin
  inverse(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)

  f ⋅ inverse(f) == id(A) ⊣ (A::Ob, B::Ob, f::(A → B))
  inverse(f) ⋅ f == id(B) ⊣ (A::Ob, B::Ob, f::(A → B))
end

@syntax FreeGroupoid{ObExpr,HomExpr} ThGroupoid begin
  compose(f::Hom, g::Hom) = associate_id_inverse(new(f,g; strict=true), id,
                                                 inverse)
  inverse(f::Hom) = distribute_unary(involute(new(f)), inverse, compose,
                                     unit=id, contravariant=true)
end
