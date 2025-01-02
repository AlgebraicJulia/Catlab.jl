module OpFinFunctor 

export OppositeFinFunctor

using StructEquality
using GATlab

using ...Categories: Cat, obtype, homtype, dom, codom
import ...Categories: op
using ...FinCats: FinCat, gentype

using ..FinFunctors: ThFinDomFunctor, FinDomFunctor, ob_map, gen_map

""" Opposite functor, given by the same mapping between opposite categories.

Call `op(::FinDomFunctor)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeFinDomFunctor{DO,CO,DH,CH,DG, C}
  func::FinDomFunctor
  function OppositeFinDomFunctor(f::FinDomFunctor) 
    D, C = dom(f), codom(f)
    CT = impl_type(f, :Cat′)
    new{obtype(D), obtype(C), homtype(C), homtype(C), gentype(D), CT}(f)
  end
end

# Accessor 
##########

GATlab.getvalue(F::OppositeFinDomFunctor) = F.func

# Constructors
##############
op(f::FinDomFunctor) = if getvalue(f) isa OppositeFinDomFunctor 
  getvalue(getvalue(f)) # optimization
else 
  FinDomFunctor(OppositeFinDomFunctor(f))
end

# FinDomFunctor instance
#########################
@instance ThFinDomFunctor{DO,CO,DH,CH,DG,FinCat,C} [model::OppositeFinDomFunctor{DO,CO,DH,CH,DG,C}
                                     ] where {DO,CO,DH,CH,DG,C} begin 
  dom()::FinCat = op(dom(getvalue(model)))

  codom()::C = op(codom(getvalue(model)))

  ob_map(x::DO)::CO = ob_map(getvalue(model), x) 

  gen_map(f::DG)::CH = hom_map(getvalue(model), f) 
end

# do_compose(F::OppositeFinDomFunctor, G::OppositeFinDomFunctor) =
#   OppositeFunctor(do_compose(F.func, G.func))


end # module
