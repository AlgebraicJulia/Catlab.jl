module CompFinFunctor 

export CompositeFinDomFunctor 

using StructEquality
using GATlab

using ...Cats
using ..FinFunctors
import ...Cats: Functor 
import ..FinFunctors: FinDomFunctor


""" Composite of functors with a finitely presented domain.
"""
@struct_hash_equal struct CompositeFinDomFunctor{AO,CO,AH,CH,AG,C}
  fst::FunctorFinDom
  snd::AbsFunctor
  function CompositeFinDomFunctor(fst::FunctorFinDom,snd::AbsFunctor)
    dom(snd) == codom(fst) || error("Cannot compose")
    AO,  AH,  AG = impl_type.(Ref(fst), [:DomOb, :DomHom, :DomGen])
    CO,CH,C = impl_type.(Ref(snd), [:CodomOb, :CodomHom, :CodCat])
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

"""
A composite of functors A -> B and B -> C
"""
@instance ThFinDomFunctor{A_Ob,C_Ob,A_Hom,C_Hom,FinCat,C,A_Gen} [
    model::CompositeFinDomFunctor{A_Ob,C_Ob,A_Hom,C_Hom,A_Gen,C}
    ] where {A_Ob,C_Ob,A_Hom,C_Hom,A_Gen,C} begin

  dom()::FinCat = dom(first(model))

  codom()::C = codom(last(model))

  ob_map(x::A_Ob)::C_Ob = ob_map(last(model), ob_map(first(model), x))
  
  hom_map(x::A_Hom)::C_Hom = hom_map(last(model), hom_map(first(model), x))

  gen_map(x::A_Gen)::C_Hom = hom_map(last(model), gen_map(first(model), x))
end


# Convenience constructors
##########################
function FinDomFunctor(F::FinDomFunctor, G::FinDomFunctor)
  getvalue(F) isa IdentityFinDomFunctor && return G
  getvalue(G) isa IdentityFinDomFunctor && return F
  FinDomFunctor′(CompositeFinDomFunctor(F,G)) |> validate
end

function Functor(F::FinDomFunctor, G::FinDomFunctor)
  FinDomFunctor′(FinFunctorAsFunctor(FinDomFunctor(F,G))) |> validate
end

end # module
