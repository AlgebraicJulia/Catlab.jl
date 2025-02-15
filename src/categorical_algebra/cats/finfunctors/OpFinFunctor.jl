module OpFinFunctor 

export OppositeFinFunctor

using StructEquality
using GATlab

using ...Cats
import ...Categories: op
using ..FinFunctors

""" Opposite functor, given by the same mapping between opposite categories.

Call `op(::FinDomFunctor)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeFinDomFunctor{DO,CO,DH,CH,DG, C}
  func::FinDomFunctor
  function OppositeFinDomFunctor(f::FinDomFunctor) 
    D, C = dom(f), codom(f)
    O,O′,H,H′,G,CT = impl_type.([D,C,D,C,D,f], [:Ob,:Ob,:Hom,:Hom,:Gen,:Cat′])
    new{O,O′,H,H′,G,CT}(f)
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

@instance ThFinDomFunctor{DO,CO,DH,CH,DG,FinCat,C
                         } [model::OppositeFinDomFunctor{DO,CO,DH,CH,DG,C}
                           ] where {DO,CO,DH,CH,DG,C} begin 
  dom()::FinCat = op(dom(getvalue(model)))

  codom()::C = op(codom(getvalue(model)))

  ob_map(x::DO)::CO = ob_map(getvalue(model), x) 

  gen_map(f::DG)::CH = gen_map(getvalue(model), f) 

end

end # module
