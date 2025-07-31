module SetFunctions 

export SetFunction, SetFunction′, ThFunctionCore, ThSetFunction, dom, codom, show_domains, specialize

using StructEquality

using GATlab
import ACSets.Columns: preimage 

import ....Theories: dom, codom
using ..Sets
using ..FinSets: FinSet#, FinSetInt

# Theory of SetFunctions
########################

""" This is only subtyped by SetFunction """
abstract type SetFunction′ end 

""" Common theory to SetFunction/Fin(Dom)Function """ 
@theory ThFunctionCore begin
  Dom::TYPE
  Cod::TYPE
  app(e::Dom)::Cod
end

"""
A SetFunction is anything that can play the role of a morphism in the category 
Set. This means we can pick out a domain and codomain set, we apply the function
to any domain element to get a codomain element, and we and turn a sequence of 
SetFunctions into a single one. In principle SetFunctions need not know anything
about composition: the composite of any two SetFunction is a `CompositeFunction` 
implementation. However, we often want to simplify a `CompositeFunction` into a 
more compressed form (which would be more efficient if one were repeatedly 
calling the function). So implementations are also required to have a method 
which is used (within `force`) to simplify a `CompositeFunction`. One could 
demand both pre- and post-composition operations, but just one suffices to 

Often, implementations are naturally postcomposed with another function, because 
this allows one to keep the same structure but just update the values. However,
there are _some_ function implementations which do fundamentally change upon 
postcomposition, such as an `IdentityFunction`. Also, in the case of  
`ConstantFunction`s, one more efficiently represents a postcomposition not by 
mapping over the structure with the same value but by just replacing the
function with another `ConstantFunction`. `postcompose` is only ever called when
using `force` to evaluate a `CompositeFunction`.
"""
@theory ThSetFunction <: ThFunctionCore begin
  Fun′::TYPE{SetFunction′}
  DomSet::TYPE{SetOb}
  CodSet::TYPE{SetOb}
  dom()::DomSet # eltype(dom()) <: Dom
  codom()::CodSet # eltype(codom()) <: Cod
  postcompose(t::Fun′)::Fun′
end


# Wrapper type for models of ThSetFunction
##########################################

""" Generic type for morphism in the category **Set**.

Note: This type would be better called simply `Function` but that name is
already taken by the base Julia type.
"""
ThSetFunction.Meta.@wrapper SetFunction <: SetFunction′

function validate(s::SetFunction)
  Dom, Codom = impl_types(s)
  eltype(dom(s)) <: Dom || error("Bad dom type")
  eltype(codom(s)) <: Codom || error("Bad cod type")
end

""" In general, we cannot take the preimage of a set function (it may be 
infinite). But for special cases, we may be. """
preimage(s::SetFunction, v) = preimage(getvalue(s), v)

# SetFunction(s::SetFunction) = s

(f::SetFunction)(x) = ThSetFunction.app(f, x)

Base.show(io::IO, f::SetFunction) = show(io, getvalue(f)) 

function show_domains(io::IO, f; domain::Bool=true, 
    codomain::Bool=true, recurse::Bool=true)
  get(io, :hide_domains, false) && return print(io, "…")
  domain && show(IOContext(io, :compact=>true, :hide_domains=>!recurse), dom[f]())
  domain && codomain && print(io, ", ")
  codomain && show(IOContext(io, :compact=>true, :hide_domains=>!recurse), codom[f]())
end

end # module
