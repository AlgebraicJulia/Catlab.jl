""" This depends on FinSets, so must come afterwards """
module DiscreteCats 

export DiscreteCat

import ..Categories: ob, hom, dom, codom, compose, id, ob_map, hom_map

""" Discrete category on a finite set.

The only morphisms in a discrete category are the identities, which are here
identified with the objects.
"""
@struct_hash_equal struct DiscreteCat{Ob,Any} <: FinCat{Ob,Ob}
  set::FinSet
end
DiscreteCat(n::Integer) = DiscreteCat(FinSet(n))

FinCat(s::Union{FinSet,Integer}) = DiscreteCat(s)

ob_generators(C::DiscreteCat) = C.set
hom_generators(::DiscreteCat) = ()
ob_generator(C::DiscreteCat, x) = x ∈ C.set ? x : error("$x ∉ $(C.set)")
ob_generator_name(C::DiscreteCat, x) = x
hom(C::DiscreteCat, x) = ob_generator(C, x)

is_discrete(::DiscreteCat) = true
graph(C::DiscreteCat{Int,FinSetInt}) = Graph(length(C.set))

dom(C::DiscreteCat{T}, f) where T = f::T
codom(C::DiscreteCat{T}, f) where T = f::T
id(C::DiscreteCat{T}, x) where T = x::T
compose(C::DiscreteCat{T}, f, g) where T = (f::T == g::T) ? f :
  error("Nontrivial composite in discrete category: $f != $g")

hom_map(F::FinDomFunctor{<:DiscreteCat}, x) = id(codom(F), ob_map(F, x))

Base.show(io::IO, C::DiscreteCat{Int,FinSetInt}) =
  print(io, "FinCat($(length(C.set)))")

end # module