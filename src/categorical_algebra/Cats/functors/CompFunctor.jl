module CompFunctor 
export CompositeFunctor

using StructEquality

import .....Theories: dom, codom
using ..Categories, ..Functors 
import ..Functors: do_ob_map, do_hom_map, do_compose


""" Composite of functors.
"""
@struct_hash_equal struct CompositeFunctor{Dom,Codom,
    F<:Functor{Dom,<:Cat},G<:Functor{<:Cat,Codom}} <: Functor{Dom,Codom}
  fst::F
  snd::G
end
Base.first(F::CompositeFunctor) = F.fst
Base.last(F::CompositeFunctor) = F.snd

dom(F::CompositeFunctor) = dom(first(F))
codom(F::CompositeFunctor) = codom(last(F))

do_ob_map(F::CompositeFunctor, x) = ob_map(F.snd, ob_map(F.fst, x))
do_hom_map(F::CompositeFunctor, f) = hom_map(F.snd, hom_map(F.fst, f))

function Base.show(io::IO, F::CompositeFunctor)
  print(io, "compose(")
  show(io, first(F))
  print(io, ", ")
  show(io, last(F))
  print(io, ")")
end

end # module