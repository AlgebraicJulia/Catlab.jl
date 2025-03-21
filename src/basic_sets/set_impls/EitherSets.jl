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
@struct_hash_equal struct EitherSet{L<:AbsSet, R<:AbsSet}
  left::L
  right::R
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
  false 
end

set_eltype(model::EitherSet) = 
  Union{Left{eltype(left(model))}, Right{eltype(right(model))}}

@instance ThSet [model::EitherSet{FinSet,SetOb}] begin

  contains(i::Any)::Bool = set_contains(model, i)

  eltype()::Any = set_eltype(model)

end

@instance ThSet [model::EitherSet{SetOb,FinSet}] begin

  contains(i::Any)::Bool = set_contains(model, i)

  eltype()::Any = set_eltype(model)

end

@instance ThSet [model::EitherSet{SetOb,SetOb}] begin

  contains(i::Any)::Bool = set_contains(model, i)

  eltype()::Any = set_eltype(model)

end


@instance ThFinSet [model::EitherSet{FinSet,FinSet}] begin

  contains(i::Any)::Bool = set_contains(model, i)

  eltype()::Any = set_eltype(model)

  length()::Int = length(left(model)) + length(right(model))

  iterator()::Any = [left(model)...,right(model)...]

end

# Constructors
##############

either(a::SetOb, b::SetOb) = SetOb(EitherSet(a,b))
either(a::FinSet, b::SetOb) = SetOb(EitherSet(a,b))
either(a::SetOb, b::FinSet) = SetOb(EitherSet(a,b))
either(a::FinSet, b::FinSet) = FinSet(EitherSet(a,b))

end # module