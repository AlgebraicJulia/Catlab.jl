
""" Functor defined by two Julia callables, an object map and a morphism map.
"""
@struct_hash_equal struct FunctorCallable{
    DO,CO,DH,CH,DC<:AbsCat{DO,DH},CC<:AbsCat{CO,CH}
    } <: FunctorImpl{DO,CO,DH,CH,DC,CC}
  ob_map::Any
  hom_map::Any
  dom::DC
  codom::CC
end

@instance ThFunctor{DO,CO,DH,CH,DH,CH,CC,DC
                   } [model::FunctorCallable{DO,CO,DH,CH,CC,DC}
                     ] where {DO,CO,DH,CH,CC,DC} begin 
  dom() = model.dom

  codom() = model.codom

  ob_map(x::DO) = model.ob_map(x) 

  hom_map(f::DH) = model.hom_map(f)
end

Functor(f::Function, g::Function, C::Cat{DO,DH}, D::Cat{CO,CH}
       ) where {DO,CO,DH,CH} = Functor(FunctorCallable(f, g, C, D))
