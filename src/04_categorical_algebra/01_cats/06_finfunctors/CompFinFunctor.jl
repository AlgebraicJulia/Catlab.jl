module CompFinFunctor 

export CompositeFinDomFunctor 

using StructEquality
using GATlab

using ...Categories: Cat, dom, codom, obtype, homtype
using ...FinCats: FinCat, gentype

using ..FinFunctors: ThFinDomFunctor, FinDomFunctor, 
                     ob_map, hom_map, gen_map
import ..FinFunctors: FinDomFunctor 
import ..IdFinFunctor: IdentityFinDomFunctor 


""" Composite of functors.
"""
@struct_hash_equal struct CompositeFinDomFunctor{AO,CO,AH,CH,AG,C}
  fst::FinDomFunctor
  snd::FinDomFunctor
  function CompositeFinDomFunctor(fst::FinDomFunctor,snd::FinDomFunctor)
    dom(snd) == codom(fst) || error("Cannot compose")
    AO,  AH,  AG = impl_type.(Ref(fst), [:DomOb, :DomHom, :DomGen])
    CO,CH,C = impl_type.(Ref(snd), [:CodomOb, :CodomHom, :Cat′])
    new{AO,CO,AH,CH,AG,C}(fst, snd)
  end
end

# Accessors
###########

Base.first(F::CompositeFinDomFunctor) = F.fst

Base.last(F::CompositeFinDomFunctor) = F.snd

# Other methods
###############
function Base.show(io::IO, F::CompositeFinDomFunctor)
  print(io, "compose(")
  show(io, first(F))
  print(io, ", ")
  show(io, last(F))
  print(io, ")")
end

# ThFinDomFunctor interface
##########################

@instance ThFinDomFunctor{AO,CO,AH,CH,AG,FinCat,C} [
    model::CompositeFinDomFunctor{AO,CO,AH,CH,AG,C}] where {AO,CO,AH,CH,AG,C} begin 
  dom() = dom(first(model))

  codom() = codom(last(model))

  ob_map(x::AO)::CO = ob_map(last(model), ob_map(first(model), x))

  gen_map(x::AG)::CH = hom_map(last(model), gen_map(first(model), x))
end


# Convenience constructors
##########################
function FinDomFunctor(F::FinDomFunctor, G::FinDomFunctor)
  getvalue(F) isa IdentityFinDomFunctor && return G
  getvalue(G) isa IdentityFinDomFunctor && return F
  FinDomFunctor(CompositeFinDomFunctor(F,G))
end

end # module
