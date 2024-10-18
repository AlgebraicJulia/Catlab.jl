""" This module contains the basic components of an Abstract Term for constructing an ADT
"""

module ADTsBase

using StructTypes
using DiagrammaticEquations
using JSON3
import Base: Dict

export AbstractTerm, _dict, typename_last

"""    AbstractTerm

The super type for all ADT types. This abstract type exists so that we can write generic methods that work on any term in any of the domain specific syntaxes.
For example, serializing to a Dictionary uses some reflection snippet that works for arbitrary types, but we only want to apply it to things that should be serialized like a Term.
"""
abstract type AbstractTerm end

"""    typename_last(T::Type)

Truncate a type name keeping only the last components of the FQTN.
"""
typename_last(T::Type) = T.name.name

_dict(x::Symbol) = x
_dict(x::String) = x
_dict(x::Number) = x
_dict(x::AbstractVector) = map(_dict, x)
_dict(x::DiagrammaticEquations.decapodes.Judgement) = x

"""    _dict(x::T) where T <: AbstractTerm

We are going to convert our structs to Dict before we call JSON3.write and 
add the type information in a generic construction. This uses some reflection 
to ask the julia type for its fieldnames and then use those as the keys in the Dict.
We use splatting, so don't make a struct with more than 32 fields if you want to go fast.
We use this _dict function to avoid an "I'm the captain now" level of type piracy.
"""
function _dict(x::T) where {T<:AbstractTerm}
  Dict(:_type => typename_last(T), [k=>_dict(getfield(x, k)) for k in fieldnames(T)]...)
end

"""    Dict(x::AbstractTerm)

to register your type with JSON3, you need to overload JSON3.write to use this Dict approach.
we only overload the Dict function for our type Formula, so this is not piracy.
"""
Dict(x::AbstractTerm) = _dict(x)

"""    JSON3.write

Now JSON3.write(f) puts the type information in our reserved field.
"""
JSON3.write(f::AbstractTerm) = JSON3.write(Dict(f))

"""    StructTypes.StructType

This is how you tell StructTypes to use an interface for you.
"""
StructTypes.StructType(::Type{AbstractTerm}) = StructTypes.AbstractType()

"""    StructTypes.subtypekey

This is how you tell StructTypes where to look for the name of a type when reading the type back in from JSON.
"""
StructTypes.subtypekey(::Type{AbstractTerm}) = :_type
end