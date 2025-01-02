module CatsInterop 
export U_CatSet

using ....BasicSets: FinDomFunction
using ...Cats: Cat, ob_set, codom, Functor, collect_ob, Category, CatC
using ..SetCat: SetC

""" Forgetful functor Cat → Set.

Sends a category to its set of objects and a functor to its object map. 
"""
U_CatSet = Functor(o-> ob_set(o), 
                   h->FinDomFunction(collect_ob(h), ob_set(codom(h))), 
                   Category(CatC()), 
                   Category(SetC()))

# This was formerly called `Ob`

end # module
