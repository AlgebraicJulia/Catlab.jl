module EitherFSet 

export EitherFinSet

using StructEquality

using GATlab

using ..FinSets: FinSetImpl, ThFinSet
import ..FinSets: FinSet

""" Sum type """
@struct_hash_equal struct EitherFinSet <: FinSetImpl
  left::FinSet
  right::FinSet
end

# Accessors
###########

left(e::EitherFinSet) = e.left

right(e::EitherFinSet) = e.right

# FinSet Implementation
#######################

@instance ThFinSet{Bool, Any, Int} [model::EitherFinSet] begin

  in′(i::Any)::Bool = i ∈ left(model) || i ∈ right(model)

  eltype′()::Any = Union{eltype(left(model)), eltype(right(model))}

  length′()::Int = length(left(model)) + length(right(model))

  iterate′()::Any = iterate([left(model)...,right(model)...])

  iterate′(x::Any)::Any = iterate([left(model)...,right(model)...], x)
end

# Default constructor
#####################

""" Default model for a pair of finsets """
FinSet(s::FinSet, r::FinSet) = FinSet(EitherFinSet(s, r))

end # module 