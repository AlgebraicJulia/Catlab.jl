module FinDomMap 
export FinDomFunctorMap, ob_key, hom_key

using StructEquality

using GATlab
import GATlab: op

using .....BasicSets, ...FinCats, ..Functors, ..FinFunctors
using ..FinFunctors: mappairs
import ..FinFunctors: do_compose, do_hom_map, do_ob_map, hom_map, ob_map

# Mapping-based functors
#-----------------------

""" Functor out of a finitely presented category given by explicit mappings.
"""
@struct_hash_equal struct FinDomFunctorMap{Dom<:FinCat, Codom<:Cat,
    ObMap, HomMap} <: FinDomFunctor{Dom,Codom}
  ob_map::ObMap
  hom_map::HomMap
  dom::Dom
  codom::Codom
end

function Base.show(io::IO, F::T) where T <: FinDomFunctorMap
  SetFunctions.show_type_constructor(io, T); print(io, "(")
  show(io, F.ob_map)
  print(io, ", ")
  show(io, F.hom_map)
  print(io, ", ")
  Categories.show_domains(io, F)
  print(io, ")")
end

FinDomFunctorMap(ob_map::Union{AbstractVector{Ob},AbstractDict{<:Any,Ob}},
                 hom_map::Union{AbstractVector{Hom},AbstractDict{<:Any,Hom}},
                 dom::FinCat) where {Ob,Hom} =
  FinDomFunctorMap(ob_map, hom_map, dom, TypeCat(Ob, Hom))

function FinDomFunctor(ob_map::Union{AbstractVector{Ob},AbstractDict{<:Any,Ob}},
                       hom_map::Union{AbstractVector{Hom},AbstractDict{<:Any,Hom}},
                       dom::FinCat, codom::Union{Cat,Nothing}=nothing) where {Ob,Hom}
  length(ob_map) == length(ob_generators(dom)) ||
    error("Length of object map $ob_map does not match domain $dom")
  length(hom_map) == length(hom_generators(dom)) ||
    error("Length of morphism map $hom_map does not match domain $dom")
  #Empty checks here are to avoid Julia blowing up the type
  if isnothing(codom)
    ob_map = isempty(ob_map) ? ob_map : mappairs(x -> ob_key(dom, x), identity, ob_map; fixvaltype = true)
    hom_map = isempty(hom_map) ? hom_map : mappairs(f -> hom_key(dom, f), identity, hom_map; fixvaltype = true)
    FinDomFunctorMap(ob_map, hom_map, dom)
  else
    ob_map = isempty(ob_map) ? ob_map : mappairs(x -> ob_key(dom, x), y -> ob(codom, y), ob_map)
    hom_map = isempty(hom_map) ? hom_map : mappairs(f -> hom_key(dom, f), g -> hom(codom, g), hom_map)
    FinDomFunctorMap(ob_map, hom_map, dom, codom)
  end
end

ob_key(C::FinCat, x) = ob_generator(C, x)
hom_key(C::FinCat, f) = hom_generator(C, f)
ob_map(F::FinDomFunctorMap) = F.ob_map
hom_map(F::FinDomFunctorMap) = F.hom_map

# Use generator names, rather than generators themselves, for Dict keys. Enforced by FinDomFunctor constructor automatically.
ob_key(C::FinCatPresentation, x) = presentation_key(x)
hom_key(C::FinCatPresentation, f) = presentation_key(f)
presentation_key(name::Union{AbstractString,Symbol}) = name
presentation_key(expr::GATExpr{:generator}) = first(expr)
ob_key(C::OppositeFinCat, x) = ob_key(C.cat,x)
hom_key(C::OppositeFinCat, f) = hom_key(C.cat,f)

Functors.do_ob_map(F::FinDomFunctorMap, x) = F.ob_map[ob_key(F.dom, x)]
Functors.do_hom_map(F::FinDomFunctorMap, f) = F.hom_map[hom_key(F.dom, f)]

function do_compose(F::FinDomFunctorMap, G::FinDomFunctorMap)
  FinDomFunctor(mapvals(x -> ob_map(G, x), F.ob_map),
                   mapvals(f -> hom_map(G, f), F.hom_map), dom(F), codom(G))
end

collect_ob(F::FinDomFunctorMap) = collect_values(F.ob_map)
collect_hom(F::FinDomFunctorMap) = collect_values(F.hom_map)
collect_values(vect::AbstractVector) = vect
collect_values(dict::AbstractDict) = collect(values(dict))

op(F::FinDomFunctorMap) = FinDomFunctorMap(F.ob_map, F.hom_map,
                                           op(dom(F)), op(codom(F)))


end # module
