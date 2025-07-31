module InclFunctions 

export InclFunction

using StructEquality
using GATlab

using ..BasicSets: SetFunction, AbsSet, SetOb, FinSet, ThFinDomFunction, 
                   ThSetFunction, ThFinFunction, FinFunction, FinFunction′, 
                   FinDomFunction′, SetFunction′
using .ThFinFunction


""" 
A pair of sets, one taken to be a subset of the other (something which can be 
checked when the subset is finite, but otherwise must be taken on faith).

This is like an IdFunction but the dom and codom are allowed to be different.

Alternatively, it's like a RestrictFunction where the function is an identity.
"""
@struct_hash_equal struct InclFunction{D<:AbsSet, CD<:AbsSet, ElD, ElCD}
  dom::D
  codom::CD
  InclFunction(ss::D, s::CD) where {D<:AbsSet, CD<:AbsSet} =
    new{D,CD,eltype(ss), eltype(s)}(ss,s)
end


@instance ThSetFunction{D,C} [model::InclFunction{SetOb,SetOb,D,C}] where {D,C} begin

  dom()::SetOb = model.dom
  
  codom()::SetOb = model.codom

  app(v::D)::C = v

  postcompose(f::SetFunction′)::SetFunction′ = 
    SetFunction(SetFunction(model), f) # generic compose

end

@instance ThFinFunction{D,C} [model::InclFunction{FinSet,FinSet,D,C}] where {D,C} begin

  dom()::FinSet = model.dom
  
  codom()::FinSet = model.codom

  app(v::D)::C = v

  postcompose(f::FinFunction′)::FinFunction′ =
    FinFunction(FinFunction(model), f)

end


@instance ThFinDomFunction{D,C} [model::InclFunction{FinSet,SetOb,D,C}] where {D,C} begin

  dom()::FinSet = model.dom
  
  codom()::SetOb = model.codom

  app(v::D)::C = v

  postcompose(f::SetFunction′)::FinDomFunction′ = 
    error("TODO")

end

end # module
