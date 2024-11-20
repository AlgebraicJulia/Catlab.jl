module IdFinFunctor

export IdentityFinDomFunctor

using StructEquality
using GATlab

using ..FinFunctors: FinDomFunctorImpl, ThFinDomFunctor
using ...Categories: Cat, FinCat, obtype, homtype, gentype
import ..FinFunctors: FinDomFunctor

""" Identity functor on a category.
"""
@struct_hash_equal struct IdentityFinDomFunctor{O,H,G} <: FinDomFunctorImpl{O,O,H,H,G}
  dom::FinCat
  IdentityFinDomFunctor(c::FinCat) = new{obtype(c), homtype(c), gentype(c)}(c)
end

GATlab.getvalue(i::IdentityFinDomFunctor) = i.dom

function Base.show(io::IO, F::IdentityFinDomFunctor)
  print(io, "id(")
  #show_domains(io, F, codomain=false) #TODO
  print(io, ")")
end

@instance ThFinDomFunctor{O,O,H,H,G,FinCat,Cat} [model::IdentityFinDomFunctor{O,H,G}] where {O,H,G} begin 
  dom() = getvalue(model)

  codom() = getvalue(model)

  ob_map(x::O)::O = x

  gen_map(x::G)::H = compose(getvalue(model), Path{O,G}([x]))
end

# Convenience constructors
##########################

FinDomFunctor(c::FinCat) = FinDomFunctor(IdentityFinDomFunctor(c))


end # module
