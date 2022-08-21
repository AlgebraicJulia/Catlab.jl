export ThGroupoid, inverse

# Groupoid
##########

""" Theory of *groupoids*.
"""

@theory ThGroupoid{Ob,Hom} <: ThCategory{Ob,Hom} begin
  inverse(f::(A → B))::(B → A) ⊣ (A::Ob, B::Ob)

  f ⋅ inverse(f) == id(A) ⊣ (A::Ob, B::Ob, f::(A → B))
  inverse(f) ⋅ f == id(B) ⊣ (A::Ob, B::Ob, f::(A → B))
end
