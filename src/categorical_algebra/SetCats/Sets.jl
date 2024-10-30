""" Category of (possibly infinite) sets and functions.

This module defines generic types for the category of sets ([`SetOb`](@ref),
[`SetFunction`](@ref)), as well as a few basic concrete types, such as a wrapper
type to view Julia types as sets ([`TypeSet`](@ref)). Extensive support for
finite sets is provided by another module, [`FinSets`](@ref).
"""
module Sets
export AbsSet, SetOb, TypeSet, PredicatedSet, EitherSet

using StructEquality

using GATlab
import ....Theories: Ob
import ...Cats.FreeDiagrams: left, right
using ...Cats.Categories: Cat

# Theory of Sets
################

@theory ThSet′ begin
  Bool′::TYPE
  Any′::TYPE
  in′(e::Any′)::Bool′
  eltype′()::Any′
end

const M = Model{Tuple{Bool, Any}} # shorthand

abstract type AbsSet end

abstract type SetImpl <: M end 

"""
Generic type for a set. It has some implementation of the theory of sets and 
a model which provides the information for how it implements the theory.
"""
@struct_hash_equal struct SetOb <: AbsSet
  impl::SetImpl
  SetOb(i::SetImpl) = implements(i, ThSet′) ? new(i) : throw(MethodError(
    "Bad model $i"))
end

GATlab.getvalue(s::SetOb) = s.impl

Base.in(e, s::SetOb) = ThSet′.in′[getvalue(s)](e)

Base.eltype(s::SetOb) = ThSet′.eltype′[getvalue(s)]()

Base.show(io::IO, s::SetOb) = show(io, getvalue(s))

# Implementations
#################

# TypeSets
#---------

""" Raw Julia type considered as a set"""
@struct_hash_equal struct TypeSet{T} <: SetImpl end

TypeSet(T::Type) = TypeSet{T}()

Base.show(io::IO, ::TypeSet{T}) where T = print(io, "TypeSet($T)")

# ThSet implementation 

@instance ThSet′{Bool, Any} [model::TypeSet{T}] where T begin
  in′(i::Any)::Bool = i isa T
  eltype′()::Any = T
end

# Default models

""" Default model for a Set made out of a Julia `Type` """
SetOb(T::Type) = SetOb(TypeSet{T}())


""" Forgetful functor Ob: Cat → Set.

Sends a category to its set of objects and a functor to its object map.
"""
Ob(::Cat{O,H}) where {O,H} = SetOb(O)

# EitherSets
#-----------

""" Sum type """
@struct_hash_equal struct EitherSet <: SetImpl
  left::AbsSet
  right::AbsSet
end

left(e::EitherSet) = e.left
right(e::EitherSet) = e.right

# ThSet implementation

@instance ThSet′{Bool, Any} [model::EitherSet] begin
  in′(i::Any)::Bool = i ∈ left(model) || i ∈ right(model)
  eltype′()::Any = Union{eltype(left(model)), eltype(right(model))}
end

SetOb(x::AbsSet, y::AbsSet) = SetOb(EitherSetImpl(x, y))

# Predicated sets
#----------------

""" Set defined by a predicate (boolean-valued function) on a Julia data type.
"""
@struct_hash_equal struct PredicatedSet{T} <: SetImpl
  predicate::Any

  PredicatedSet{T}(f) where T = new{T}(f)
end

PredicatedSet(T::Type, f) = PredicatedSet{T}(f)

""" Apply the predicate """
function (s::PredicatedSet{T})(x::T)::Bool where {T}
  s.predicate(x)
end

function Base.show(io::IO, s::PredicatedSet{T}) where T
  print(io, "PredicatedSet($T, $(nameof(s.predicate)))")
end

# ThSet implementation 
@instance ThSet′{Bool, Any} [model::PredicatedSet{T}] where T begin
  in′(i::Any)::Bool = i isa T && model(i)
  eltype′()::Any = T
end

end # module
