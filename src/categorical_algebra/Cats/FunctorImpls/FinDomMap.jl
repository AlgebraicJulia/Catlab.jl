
""" View Vectors equivalently as Int-keyed Dictionaries """
const VD{K,V} = Union{AbstractVector{V},AbstractDict{K,V}}

""" Functor out of a finitely presented category given by explicit mappings.
"""
@struct_hash_equal struct FinDomFunctorMap{DO,CO,DH,CH,DG,CG,
    Dom<:FinCat{DO,DH,DG}, Codom<:AbsCat{CO,CH}, ObMap, HomMap
    } <: FinDomFunctorImpl{DO,CO,DH,CH,DG,CG,Dom,Codom}
  ob_map::ObMap
  hom_map::HomMap
  dom::Dom
  codom::Codom
end

""" Construct FinDomFunctorMap from two vectors """
FinDomFunctorMap(om::OM, hm::HM, d::D, c::C
                ) where {DH,CO,CH,CG,OM<:AbstractVector{<:CO}, 
                         HM<:AbstractVector{<:CH},D<:FinCat{Int,DH,Int},
                         C<:FinCat{CO,CH,CG}} = 
  FinDomFunctorMap{Int,CO,DH,CH,Int,CG,D,C,OM,HM}(om,hm,d,c)

""" 
Construct FinDomFunctorMap from two vectors. Hom vector given in terms of 
codom generators. 
"""
function FinDomFunctorMap(om::OM, hm::HM, d::D, c::C
                ) where {DH,CO,CH,CG,OM<:AbstractVector{<:CO}, 
                         HM<:AbstractVector{<:AbstractVector{<:CG}},
                         D<:FinCat{Int,DH,Int},
                         C<:FinCat{CO,CH,CG}} 
  v= CH[compose(c, h) for h in hm]
  FinDomFunctorMap{Int,CO,DH,CH,Int,CG,D,C,OM,typeof(v)}(om,v,d,c)
end 
""" Construct FinDomFunctorMap from two dictionaries """
FinDomFunctorMap(om::OM, hm::HM, d::D, c::C
                ) where {DO,DH,DG,CO,CH,CG,OM<:AbstractDict{<:DO,<:CO}, 
                         HM<:AbstractDict{<:DG,<:CH},D<:FinCat{DO,DH,DG},
                         C<:FinCat{CO,CH,CG}} = 
  FinDomFunctorMap{DO,CO,DH,CH,DG,CG,D,C,OM,HM}(om,hm,d,c)

@instance ThFunctor{DO,CO,DH,CH,DG,CG,CC,DC
                   } [model::FinDomFunctorMap{DO,CO,DH,CH,DG,CG,CC,DC,OM,HM}
                     ] where {DO,CO,DH,CH,DG,CG,CC,DC,OM,HM} begin 
  dom() = model.dom

  codom() = model.codom

  ob_map(x::DO) = model.ob_map[x]  

  hom_map(f::DG) = model.hom_map[f]
end

function FinDomFunctor(ob_map::Union{<:AbstractVector,<:AbstractDict}, 
                       hom_map::Union{<:AbstractVector,<:AbstractDict},
                       dom::FinCat{DO,DH,DG}, 
                       codom::Union{AbsCat{CO,CH},Nothing}=nothing
                       ) where {DO,DH,DG,CO,CH}
  length(ob_map) == length(ob_generators(dom)) ||
    error("Length of object map $ob_map does not match domain $dom")
  length(hom_map) == length(hom_generators(dom)) ||
    error("Length of morphism map $hom_map does not match domain $dom")
  # NOTE: removed the empty checks which avoid Julia blowing up the type
  codom = isnothing(codom) ? Cat(TypeCat{CO,CH}()) : codom
  FinDomFunctorMap(ob_map, hom_map, dom, codom) |> Functor
end


FinDomFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCat, codom::AbsCat) =
  if getvalue(dom) isa FinCatGraph 
    FinDomFunctor(maps.V, maps.E, dom, codom)
  else 
    error("bad maps $maps for dom $dom")
  end

function FinDomFunctor(ob_map, dom::FinCat, codom::AbsCat{Ob,Hom}) where {Ob,Hom}
  is_discrete(dom) ||
    error("Morphism map omitted by domain category is not discrete: $dom")
  FinDomFunctor(FinDomFunctorMap(ob_map, empty(ob_map, Hom), dom, codom))
end

FinDomFunctor(ob_map, ::Nothing, dom::FinCat, codom::AbsCat) =
  FinDomFunctor(ob_map, dom, codom)