
module UnionSets

export UnionSet, left, right

using StructEquality

using GATlab

using ..Sets: ThSet′, AbsSet

""" Union type """
@struct_hash_equal struct UnionSet
  sets::AbstractVector{AbsSet}
end

# Accessors
###########

Base.iterate(e::UnionSet, i...) = iterate(e.sets, i...)

left(e::UnionSet) = first(e.sets)

right(e::UnionSet) = last(e.sets)

# ThSet implementation
######################

@instance ThSet′{Bool, Any} [model::UnionSet] begin

  in′(i::Any)::Bool = any(s->i ∈ s, model.sets)

  eltype()::Any = Union{eltype.(model)...}

end

end # module
