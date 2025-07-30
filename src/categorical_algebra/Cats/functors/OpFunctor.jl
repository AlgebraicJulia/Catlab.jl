module OpFunctor 
export OppositeFunctor

using StructEquality

import GATlab: op

import .....Theories: dom, codom
using ..Functors 
import ..Functors: do_ob_map, do_hom_map, do_compose

""" Opposite functor, given by the same mapping between opposite categories.

Call `op(::Functor)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeFunctor{C,D,F<:Functor{C,D}} <: Functor{C,D}
    # XXX: Requires more type parameters: ObC, HomC, ObD, HomD.
    #Functor{OppositeCat{C},OppositeCat{D}}
  func::F
end

dom(F::OppositeFunctor) = op(dom(F.func))
codom(F::OppositeFunctor) = op(codom(F.func))

do_ob_map(F::OppositeFunctor, x) = ob_map(F.func, x)
do_hom_map(F::OppositeFunctor, f) = hom_map(F.func, f)

do_compose(F::OppositeFunctor, G::OppositeFunctor) =
  OppositeFunctor(do_compose(F.func, G.func))


op(F::Functor) = OppositeFunctor(F)
op(F::OppositeFunctor) = F.func

end # module
