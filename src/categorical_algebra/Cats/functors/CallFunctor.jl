module CallFunctor
export FunctorCallable

using StructEquality

import .....Theories: dom, codom
using ..Categories, ..Functors 
import ..Functors: do_ob_map, do_hom_map, do_compose, Functor


""" Functor defined by two Julia callables, an object map and a morphism map.
"""
@struct_hash_equal struct FunctorCallable{Dom,Codom} <: Functor{Dom,Codom}
  ob_map::Any
  hom_map::Any
  dom::Dom
  codom::Codom
end

dom(F::FunctorCallable) = F.dom
codom(F::FunctorCallable) = F.codom
do_ob_map(F::FunctorCallable, x) = F.ob_map(x)
do_hom_map(F::FunctorCallable, f) = F.hom_map(f)
ob_map(f::FunctorCallable) = f.ob_map
hom_map(f::FunctorCallable) = f.hom_map

Functor(f::Function, g::Function, C::Cat, D::Cat) = FunctorCallable(f, g, C, D)

end # module
