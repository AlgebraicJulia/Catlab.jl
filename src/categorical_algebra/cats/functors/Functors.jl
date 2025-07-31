export Functor, ob_map, hom_map, ThFunctor, fmap, AbsFunctor

using StructEquality
using GATlab

using ..Categories: Cat, obtype, homtype
import ..Categories: dom, codom, validate, ob_map, hom_map

# Theory of functors
####################

# The equations that come with this will be less tedious to do when colimits 
# of GATs are a thing. We also wouldn't need a "Cat" type.
@theory ThFunctor begin
  DomOb::TYPE; CodomOb::TYPE; DomHom::TYPE; CodomHom::TYPE;
  DomCat::TYPE; CodCat::TYPE;
  dom()::DomCat
  codom()::CodCat
  ob_map(o::DomOb)::CodomOb
  hom_map(o::DomHom)::CodomHom
end

""" Common type for Functor, FinFunctor, FinDomFunctor """
abstract type AbsFunctor end 

""" Functor between categories.

A functor has a domain and a codomain ([`dom`](@ref) and [`codom`](@ref)), which
are categories, and object and morphism maps, which can be evaluated using
[`ob_map`](@ref) and [`hom_map`](@ref). The functor object can also be called
directly when the objects and morphisms have distinct Julia types. This is
sometimes but not always the case (see [`Category`](@ref)), so when writing
generic code one should prefer the `ob_map` and `hom_map` functions.
"""
ThFunctor.Meta.@typed_wrapper Functor′ <: AbsFunctor

const Functor{A,B,C,D} = Functor′{A,B,C,D,Cat,Cat}

Functor(x) = Functor′(x)

"""
Wrapper of an implementation of ThFunctor
"""
function validate(f::Functor)
  DO, CO, DH, CH = impl_type.(Ref(f),[:DomOb,:CodomOb,:DomHom, :CodomHom])
  D, C = ThFunctor.dom[impl](), ThFunctor.codom[impl]()
  obtype(D) == DO || error("Bad dom obtype")
  homtype(D) == DH || error("Bad dom obtype $(homtype(D)) ≠ $DH")
  obtype(C) == CO || error("Bad dom obtype")
  homtype(C) == CH || error("Bad dom obtype")
end 


# Other methods
#--------------

Base.show(io::IO, s::Functor) = show(io, getvalue(s))

show_type_constructor(io::IO, ::Type{<:Functor}) = print(io, "Functor")

function show_domains(io::IO, f; domain::Bool=true, codomain::Bool=true,
                      recurse::Bool=true)
  if get(io, :hide_domains, false)
    print(io, "…")
  else
    if domain
      show(IOContext(io, :compact=>true, :hide_domains=>!recurse), dom(f))
    end
    if codomain
      domain && print(io, ", ")
      show(IOContext(io, :compact=>true, :hide_domains=>!recurse), codom(f))
    end
  end
end

fmap(F::Functor, x) = fmap(x, 
                           y->ob_map(F, y), 
                           y->hom_map(F, y), 
                           impl_type(F, :CodomOb), 
                           impl_type(F, :CodomHom))
