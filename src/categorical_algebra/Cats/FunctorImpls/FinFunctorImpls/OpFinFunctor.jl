module OpFinFunctor 

export OppositeFinFunctor

using StructEquality
using GATlab
import GATlab: op, getvalue

using ...Categories: FinCat, Cat, dom, codom, obtype, homtype, gentype
                     
using ..FinFunctors: FinDomFunctorImpl, ThFinDomFunctor, FinDomFunctor,
                     ob_map, gen_map

""" Opposite functor, given by the same mapping between opposite categories.

Call `op(::FinDomFunctor)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeFinDomFunctor{DO,CO,DH,CH,DG} <: FinDomFunctorImpl{DO,CO,DH,CH,DG}
  func::FinDomFunctor
  function OppositeFinDomFunctor(f::FinDomFunctor) 
    D, C = dom(f), codom(f)
    new{obtype(D), obtype(C), homtype(C), homtype(C), gentype(D)}(f)
  end
end

# Accessor 
##########

getvalue(F::OppositeFinDomFunctor) = F.func

# Constructors
##############
op(f::FinDomFunctor) = if getvalue(f) isa OppositeFinDomFunctor 
  getvalue(getvalue(f)) # optimization
else 
  FinDomFunctor(OppositeFinDomFunctor(f))
end

# FinDomFunctor instance
#########################
@instance ThFinDomFunctor{DO,CO,DH,CH,DG,FinCat,Cat} [model::OppositeFinDomFunctor{DO,CO,DH,CH,DG}
                                     ] where {DO,CO,DH,CH,DG} begin 
  dom() = op(dom(getvalue(model)))

  codom() = op(codom(getvalue(model)))

  ob_map(x::DO)::CO = ob_map(getvalue(model), x) 

  gen_map(f::DG)::CH = hom_map(getvalue(model), f) 
end

# do_compose(F::OppositeFinDomFunctor, G::OppositeFinDomFunctor) =
#   OppositeFunctor(do_compose(F.func, G.func))


end # module
