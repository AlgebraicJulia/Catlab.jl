
module UnionSets

export UnionSet, left, right

using StructEquality

using GATlab

using ..Sets: SetImpl, ThSet′, AbsSet

""" Union type """
@struct_hash_equal struct UnionSet <: SetImpl
  left::AbsSet
  right::AbsSet
end

# Accessors
###########

left(e::UnionSet) = e.left

right(e::UnionSet) = e.right

# ThSet implementation
######################

@instance ThSet′{Bool, Any} [model::UnionSet] begin

  in′(i::Any)::Bool = i ∈ left(model) || i ∈ right(model)

  eltype′()::Any = Union{eltype(left(model)), eltype(right(model))}

end

end # module
