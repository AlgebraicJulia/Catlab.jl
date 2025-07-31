module EitherSets 

export EitherSet, Left, Right, either

using StructEquality

using GATlab

using ..BasicSets: ThSet, ThFinSet, SetOb, FinSet, AbsSet
import ..UnionSets: left, right

# Helper methods 
################
GATlab.getvalue(l::Left) = l.val

GATlab.getvalue(r::Right) = r.val

Base.isless(x::Left, y::Left) = isless(getvalue(x), getvalue(y))

Base.isless(x::Right, y::Right) = isless(getvalue(x), getvalue(y))

# Model data type
#################

""" 
Disjoint union type. In order to not conflate values, we need to wrap one 
of the sets in `Left` and one in `Right`. 
"""
@struct_hash_equal struct EitherSet{L<:AbsSet, R<:AbsSet, T}
  left::L
  right::R
  EitherSet(l::L,r::R) where {L<:AbsSet, R<:AbsSet} =   
    new{L, R, Union{Left{eltype(l)}, Right{eltype(r)}}}(l, r)
end

# Accessors
###########

left(e::EitherSet) = e.left

right(e::EitherSet) = e.right

# ThSet implementation
######################
set_contains(model::EitherSet, i::Any)::Bool = if i isa Left 
  getvalue(i) ∈ left(model) 
elseif i isa Right 
  getvalue(i) ∈ right(model)
else 
  error("Impossible: $(typeof(i)) is not a Left nor Right") 
end

@instance ThSet{T} [model::EitherSet{FinSet,SetOb,T}] where T begin

  contains(i::T)::Bool = set_contains(model, i)

end

@instance ThSet{T} [model::EitherSet{SetOb,FinSet,T}] where T begin

  contains(i::T)::Bool = set_contains(model, i)

end

@instance ThSet{T} [model::EitherSet{SetOb,SetOb,T}] where T begin

  contains(i::Any)::Bool = set_contains(model, i)

end


@instance ThFinSet{T} [model::EitherSet{FinSet,FinSet,T}] where T begin

  contains(i::T)::Bool = set_contains(model, i)

  length()::Int = length(left(model)) + length(right(model))

  collect()::Vector{T} = [left(model)...,right(model)...]

end

# Constructors
##############

either(a::SetOb, b::SetOb) = SetOb(EitherSet(a,b))
either(a::FinSet, b::SetOb) = SetOb(EitherSet(a,b))
either(a::SetOb, b::FinSet) = SetOb(EitherSet(a,b))
either(a::FinSet, b::FinSet) = FinSet(EitherSet(a,b))

end # module
