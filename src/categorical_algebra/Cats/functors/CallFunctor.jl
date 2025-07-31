module CallFunctor

export FunctorCallable

using StructEquality
using GATlab

using ...Categories: Cat, obtype, homtype
using ..Functors: ThFunctor
import ..Functors: Functor


""" Functor defined by two Julia callables, an object map and a morphism map.
"""
@struct_hash_equal struct FunctorCallable{DO,CO,DH,CH}
  ob_map::Any
  hom_map::Any
  dom::Cat
  codom::Cat
  function FunctorCallable(o, h, d, c)
    (DO, CO), (DH,CH) = obtype.([d,c]), homtype.([d,c])
    new{DO,CO,DH,CH}(o, h, d, c)
  end
end

# ThFunctor implementation
##########################

@instance ThFunctor{DO,CO,DH,CH,Cat,Cat} [model::FunctorCallable{DO,CO,DH,CH} 
                                     ] where {DO,CO,DH,CH} begin 
  dom()::Cat = model.dom

  codom()::Cat = model.codom

  ob_map(x::DO) = model.ob_map(x) 

  hom_map(f::DH) = model.hom_map(f)
end

# Convenience constructor 
#########################

Functor(f::Function, g::Function, C::Cat, D::Cat) = 
  Functor(FunctorCallable(f, g, C, D))

end # module
