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
  func::FunctorFinDom
  function OppositeFinDomFunctor(f::FunctorFinDom) 
    Ts = impl_type.(Ref(f),[:DomOb,:CodomOb,:DomHom,:CodomHom,:DomGen,:CodCat])
    new{Ts...}(f)
  end
end

# Accessor 
##########

GATlab.getvalue(F::OppositeFinDomFunctor) = F.func

# Constructors
##############
op(f::F) where F<:FunctorFinDom = if getvalue(f) isa OppositeFinDomFunctor 
  getvalue(getvalue(f)) # optimization
else
  F(OppositeFinDomFunctor(f))
end

# FinDomFunctor instance
#########################

@instance ThFinDomFunctor{DO, CO, DH, CH, FinCat, C, DG
                         } [model::OppositeFinDomFunctor{DO,CO,DH,CH,DG,C}
                           ] where {DO,CO,DH,CH,DG,C} begin 
  dom()::FinCat = op(dom(getvalue(model)))

  codom()::C = op(codom(getvalue(model)))

  ob_map(x::DO)::CO = ob_map(getvalue(model), x)

  hom_map(x::DH)::CH = hom_map(getvalue(model), x) 

  gen_map(f::DG)::CH = gen_map(getvalue(model), f) 

end

end # module
