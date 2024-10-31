@struct_hash_equal struct IdentityTransformation{DO,CO,DH,CH} <: NatTransImpl{DO,CO,DH,CH}
  dom::Functor{DO,CO,DH,CH}
end

@instance ThTransformation{DO,CO,DH,CH,Functor{DO,CO,DH,CH},Functor{DO,CO,DH,CH}
                          } [model::IdentityTransformation{DO,CO,DH,CH}
                            ] where {DO,CO,DH,CH} begin
  codom() = model.dom
  dom() = model.dom
  component(x::DO) = let F = dom[model](); id(codom(F), ob_map(F, x)) end
end 


IdentityTransformation(C::Cat{Ob,Hom}) where {Ob,Hom} = 
  IdentityTransformation(IdentityFunctor(C))

Transformation(f::Functor) = Transformation(IdentityTransformation(f))

Transformation(C::Cat) = Transformation(Functor(C))