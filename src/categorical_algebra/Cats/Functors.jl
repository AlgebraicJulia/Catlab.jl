module Functors 
export Functor, ob_map, hom_map

using StructEquality
using Reexport

using GATlab
import GATlab: getvalue

using ..Categories: Cat, obtype, homtype

# Theory of functors
####################

# The equations that come with this will be less tedious to do when colimits 
# of GATs are a thing
@theory ThFunctor begin
  DomOb::TYPE; CodomOb::TYPE; DomHom::TYPE; CodomHom::TYPE;
  Cat::TYPE;
  dom()::Cat
  codom()::Cat
  ob_map(o::DomOb)::CodomOb
  hom_map(o::DomHom)::CodomHom
end

""" Any subtype of this should implement ThFunctor """
abstract type FunctorImpl{DO,CO,DH,CH} <: Model{Tuple{DO,CO,DH,CH,Cat}} end

""" Functor between categories.

A functor has a domain and a codomain ([`dom`](@ref) and [`codom`](@ref)), which
are categories, and object and morphism maps, which can be evaluated using
[`ob_map`](@ref) and [`hom_map`](@ref). The functor object can also be called
directly when the objects and morphisms have distinct Julia types. This is
sometimes but not always the case (see [`Category`](@ref)), so when writing
generic code one should prefer the `ob_map` and `hom_map` functions.
"""

"""
Wrapper of an implementation of ThFunctor
"""
@struct_hash_equal struct Functor
  impl::FunctorImpl
  function Functor(impl::FunctorImpl{DO,CO,DH,CH}) where {DO,CO,DH,CH}
    implements(impl, ThFunctor) || error("Bad model")
    D, C = ThFunctor.dom[impl](), ThFunctor.codom[impl]()
    obtype(D) == DO || error("Bad dom obtype")
    homtype(D) == DH || error("Bad dom obtype $(homtype(D)) ≠ $DH")
    obtype(C) == CO || error("Bad dom obtype")
    homtype(C) == CH || error("Bad dom obtype")
    new(impl)
  end
end 
  
getvalue(f::Functor) = f.impl

# Access theory methods
#----------------------

ob_map(F::Functor, x) = ob_map[getvalue(F)](x)

hom_map(F::Functor, x) = hom_map[getvalue(F)](x)

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

# Implementations
#################

include("FunctorImpls/IdFunctor.jl")
include("FunctorImpls/CompFunctor.jl")
include("FunctorImpls/CallFunctor.jl")
include("FunctorImpls/OpFunctor.jl")

@reexport using .IdFunctor
@reexport using .CompFunctor
@reexport using .CallFunctor
@reexport using .OpFunctor

end # module
