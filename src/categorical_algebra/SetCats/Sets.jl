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
import ...Cats.Categories: getmodel

# Theory of Sets
################

@theory ThSet′ begin
  Bool′::TYPE
  Int′::TYPE
  Any′::TYPE
  Set′::TYPE
  in′(e::Any′, s::Set′)::Bool′
  eltype′(s::Set′)::Any′
end

const M{T} = Model{Tuple{Bool, Int, Any, T}} # shorthand

abstract type AbsSet end

abstract type SetImpl end 

"""
Generic type for a set. It has some implementation of the theory of sets and 
a model which provides the information for how it implements the theory.
"""
@struct_hash_equal struct SetOb <: AbsSet
  impl::SetImpl
  mod::Any
  SetOb(i::T, m::M{T}) where {T<:SetImpl} = 
    implements(m, ThSet′) ? new(i, m) : throw(MethodError("Bad model $i $m"))
end

GATlab.getvalue(s::SetOb) = s.impl
getmodel(s::SetOb) = s.mod

Base.in(e, f::SetOb) = ThSet′.in′[getmodel(f)](e, getvalue(f))

Base.eltype(s::SetOb) = ThSet′.eltype′[getmodel(s)](getvalue(s))

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

@struct_hash_equal struct TypeSetImpl{T} <: M{TypeSet{T}} end

@instance ThSet′{Bool, Int, Any, TypeSet{T}} [model::TypeSetImpl{T}] where T begin
  in′(i::Any, s::TypeSet{T})::Bool = i isa T
  eltype′(s::TypeSet{T})::Any = T
end

# Default models

""" Default model for a Set made out of a Julia `Type` """
SetOb(T::Type) = SetOb(TypeSet{T}())
SetOb(s::TypeSet{T}) where T = SetOb(s, TypeSetImpl{T}())


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

@struct_hash_equal struct EitherSetImpl <: M{EitherSet} end

@instance ThSet′{Bool, Int, Any, EitherSet} [model::EitherSetImpl] begin
  in′(i::Any, s::EitherSet)::Bool = i ∈ left(s) || i ∈ right(s)
  eltype′(s::EitherSet)::Any = Union{eltype(left(s)), eltype(right(s))}
end

# Default ThSet model 

SetOb(s::EitherSet) = SetOb(s, EitherSetImpl())

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

@struct_hash_equal struct PredicatedSetImpl{T} <: M{PredicatedSet{T}} end

@instance ThSet′{Bool, Int, Any, PredicatedSet{T}} [model::PredicatedSetImpl{T}] where T begin
  in′(i::Any, s::PredicatedSet{T})::Bool = i isa T && s(i)
  eltype′(s::PredicatedSet{T})::Any = T
end

# Default ThSet model 

SetOb(s::PredicatedSet{T}) where T = SetOb(s, PredicatedSetImpl{T}())

end # module
