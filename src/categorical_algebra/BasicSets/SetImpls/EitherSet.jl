
module EitherSets

export EitherSet, left, right

using StructEquality

using GATlab

using ..Sets: SetImpl, ThSet′, AbsSet
import ..Sets: SetOb

""" Union type """
@struct_hash_equal struct EitherSet <: SetImpl
  left::AbsSet
  right::AbsSet
end

# Accessors
###########

left(e::EitherSet) = e.left

right(e::EitherSet) = e.right

# ThSet implementation
######################

@instance ThSet′{Bool, Any} [model::EitherSet] begin

  in′(i::Any)::Bool = i ∈ left(model) || i ∈ right(model)

  eltype′()::Any = Union{eltype(left(model)), eltype(right(model))}

end

# Default constructor for convenience
#####################################

SetOb(x::AbsSet, y::AbsSet) = SetOb(EitherSetImpl(x, y))

end # module
