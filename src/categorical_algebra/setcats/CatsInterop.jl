module CatsInterop 
export U_CatSet

using ....BasicSets, ...Cats
using ..SetCat: SetC


function hom_comp(h)
  cod = ob_set(codom(h))
  (cod isa FinSet ? FinFunction : FinDomFunction)(collect_ob(h), cod)
end

""" Forgetful functor Cat → Set.

Sends a category to its set of objects and a functor to its object map. 
"""
U_CatSet = Functor(o -> ob_set(o), hom_comp, Category(CatC()), Category(SetC()))

# This was formerly called `Ob`

end # module
