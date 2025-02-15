module IdFunctor 
export IdentityFunctor

using StructEquality

import .....Theories: dom, codom
using ..Categories, ..Functors 
import ..Functors: do_ob_map, do_hom_map, do_compose

""" Identity functor on a category.
"""
@struct_hash_equal struct IdentityFunctor{Dom<:Cat} <: Functor{Dom,Dom}
  dom::Dom
end

codom(F::IdentityFunctor) = F.dom

do_ob_map(F::IdentityFunctor, x) = ob(F.dom, x)
do_hom_map(F::IdentityFunctor, f) = hom(F.dom, f)

function Base.show(io::IO, F::IdentityFunctor)
  print(io, "id(")
  Categories.show_domains(io, F, codomain=false)
  print(io, ")")
end

end # module