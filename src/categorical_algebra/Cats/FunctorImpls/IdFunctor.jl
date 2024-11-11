module IdFunctor

export IdentityFunctor

using StructEquality
using GATlab

using ..Functors: FunctorImpl, ThFunctor
using ...Categories: Cat, obtype, homtype
import ..Functors: Functor

""" Identity functor on a category.
"""
@struct_hash_equal struct IdentityFunctor{O,H} <: FunctorImpl{O,O,H,H}
  dom::Cat
  IdentityFunctor(c::Cat) = new{obtype(c), homtype(c)}(c)
end

function Base.show(io::IO, F::IdentityFunctor)
  print(io, "id(")
  #show_domains(io, F, codomain=false) #TODO
  print(io, ")")
end

@instance ThFunctor{O,O,H,H,Cat} [model::IdentityFunctor{O,H}] where {O,H} begin 
  dom() = model.dom

  codom() = model.dom

  ob_map(x::O)::O = x

  hom_map(x::H)::H = x
end

# Convenience constructors
##########################

Functor(c::Cat) = Functor(IdentityFunctor(c))


end # module
