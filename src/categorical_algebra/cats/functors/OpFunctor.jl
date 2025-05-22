module OpFunctor 

export OppositeFunctor

using StructEquality
using GATlab

using ...Categories: Cat, dom, codom, obtype, homtype
import ...Categories: op
using ..Functors: ThFunctor, Functor, ob_map, hom_map

""" Opposite functor, given by the same mapping between opposite categories.

Call `op(::Functor)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeFunctor{DO,CO,DH,CH}
  func::Functor
  OppositeFunctor(f::Functor) = 
    new{obtype(dom(f)), obtype(codom(f)), homtype(dom(f)), homtype(codom(f))}(f)
end

GATlab.getvalue(F::OppositeFunctor) = F.func

op(f::Functor) = if getvalue(f) isa OppositeFunctor 
  getvalue(getvalue(f)) # optimization
else 
  Functor(OppositeFunctor(f))
end

@instance ThFunctor{DO,CO,DH,CH,Cat,Cat} [model::OppositeFunctor{DO,CO,DH,CH}
                                     ] where {DO,CO,DH,CH} begin 
  dom() = op(dom(getvalue(model)))

  codom() = op(codom(getvalue(model)))

  ob_map(x::DO) = ob_map(getvalue(model), x) 

  hom_map(f::DH) = hom_map(getvalue(model), f) 
end

# do_compose(F::OppositeFunctor, G::OppositeFunctor) =
#   OppositeFunctor(do_compose(F.func, G.func))


end # module
