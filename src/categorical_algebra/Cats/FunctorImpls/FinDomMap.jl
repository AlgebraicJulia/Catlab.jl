module FinDomMap 

export FinDomFunctorMap

using StructEquality

using GATlab
import GATlab: getvalue

using ...Categories: Category, FinCat, Cat, obtype, homtype, 
                     ob_generators, hom_generators, gentype
using ..FinFunctors: FinDomFunctorImpl, ThFinDomFunctor
import ..FinFunctors: FinDomFunctor

""" View Vectors equivalently as Int-keyed Dictionaries """
const VD{K,V} = Union{AbstractVector{V},AbstractDict{K,V}}

""" Functor out of a finitely presented category given by explicit mappings.
"""
@struct_hash_equal struct FinDomFunctorMap{DO,CO,DH,CH,DG, ObMap, HomMap
    } <: FinDomFunctorImpl{DO,CO,DH,CH,DG}
  ob_map::ObMap
  hom_map::HomMap
  dom::FinCat
  codom::Category
  function FinDomFunctorMap(o,h,d::FinCat,c::Union{Cat,FinCat})
    c = c isa Cat ? c : Cat(c)
    DO, CO = obtype.([d,c])
    DH, CH = homtype.([d,c])
    DG = gentype(d)
    new{DO,CO,DH,CH,DG, typeof(o), typeof(h)}(o,h,d,c)
  end
end

# FinDomFunctor instance
########################

@instance ThFinDomFunctor{DO,CO,DH,CH,DG, FinCat, Category
                          } [model::FinDomFunctorMap{DO,CO,DH,CH,DG,OM,HM}
                            ] where {DO,CO,DH,CH,DG,OM,HM} begin 
  dom() = model.dom

  codom() = model.codom

  ob_map(x::DO)::CO = model.ob_map[x]  

  gen_map(f::DG)::CH = model.hom_map[f]
end

# Constructors 
##############

const Maybe{X} = Union{Nothing, X}

function FinDomFunctor(ob_map::VD{DO,CO}, hom_map::VD{DG,CH},
                       dom::FinCat, codom::Maybe{Union{FinCat,Cat}}=nothing
                       ) where {DO,DG,CO,CH}
  length(ob_map) == length(ob_generators(dom)) ||
    error("Length of object map $ob_map does not match domain $dom")
  length(hom_map) == length(hom_generators(dom)) ||
    error("Length of morphism map $hom_map does not match domain $dom")
  # NOTE: removed the empty checks which avoid Julia blowing up the type
  codom = isnothing(codom) ? Cat(TypeCat{CO,CH}()) : codom
  FinDomFunctorMap(ob_map, hom_map, dom, codom) |> FinDomFunctor
end


# FinDomFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCat, codom::AbsCat) =
#   if getvalue(dom) isa FinCatGraph 
#     FinDomFunctor(maps.V, maps.E, dom, codom)
#   else 
#     error("bad maps $maps for dom $dom")
#   end

function FinDomFunctor(ob_map, dom::FinCat, codom::Cat)
  is_discrete(dom) ||
    error("Morphism map omitted by domain category is not discrete: $dom")
  FinDomFunctor(FinDomFunctorMap(ob_map, empty(ob_map, Hom), dom, codom))
end

FinDomFunctor(ob_map, ::Nothing, dom::FinCat, codom::Cat) =
  FinDomFunctor(ob_map, dom, codom)

# FinFunctor(maps, dom::FinCat, codom::FinCat) = FinDomFunctor(maps, dom, codom)

# FinFunctor(ob_map, hom_map, dom::FinCat, codom::FinCat) =
#   FinDomFunctor(ob_map, hom_map, dom, codom)

# FinFunctor(ob_map, hom_map, dom::Presentation, codom::Presentation) =
#   FinDomFunctor(ob_map, hom_map, FinCat(dom), FinCat(codom))

end # module
