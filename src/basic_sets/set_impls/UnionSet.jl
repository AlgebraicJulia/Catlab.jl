
module UnionSets

export UnionSet, left, right

using StructEquality

using GATlab

using ..BasicSets: ThSet, ThFinSet, AbsSet, SetOb, FinSet

""" Union type for Sets or FinSets """
@struct_hash_equal struct UnionSet{T<:AbsSet}
  sets::AbstractVector{T}
end

# Accessors
###########

Base.iterate(e::UnionSet, i...) = iterate(e.sets, i...)

left(e::UnionSet) = first(e.sets)

right(e::UnionSet) = last(e.sets)

# ThSet implementation
######################

@instance ThSet [model::UnionSet{SetOb}] begin

  contains(i::Any)::Bool = any(s->i ∈ s, model.sets)

  eltype()::Any = Union{eltype.(model)...}

end

@instance ThFinSet [model::UnionSet{FinSet}] begin

  contains(i::Any)::Bool = any(s->i ∈ s, model.sets)

  eltype()::Any = Union{eltype.(model)...}

  length()::Int = length(iterator[model]())

  iterator()::Any = union(collect.(model)...)

end


end # module
