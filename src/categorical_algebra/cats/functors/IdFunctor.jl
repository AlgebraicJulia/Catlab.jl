module IdFunctor

export IdentityFunctor

using StructEquality
using GATlab

using ...Categories: Cat, obtype, homtype
using ..Functors: ThFunctor
import ..Functors: Functor

""" Identity functor on a category.
"""
@struct_hash_equal struct IdentityFunctor{O,H}
  dom::Cat
  IdentityFunctor(c::Cat) = new{obtype(c), homtype(c)}(c)
end

GATlab.getvalue(i::IdentityFunctor) = i.dom

function Base.show(io::IO, F::IdentityFunctor)
  print(io, "id(")
  show(io, F.dom)
  print(io, ")")
end

@instance ThFunctor{O,O,H,H,Cat,Cat} [model::IdentityFunctor{O,H}] where {O,H} begin 
  dom() = getvalue(model)

  codom() = getvalue(model)

  ob_map(x::O)::O = x

  hom_map(x::H)::H = x
end

# Convenience constructors
##########################

Functor(c::Cat) = Functor(IdentityFunctor(c))

end # module
