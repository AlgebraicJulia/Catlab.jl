
module UnionSets

export UnionSet, left, right

using StructEquality

using GATlab

using ..BasicSets: ThSet, ThFinSet, AbsSet, SetOb, FinSet

""" Union type for Sets or FinSets """
@struct_hash_equal struct UnionSet{T<:AbsSet, Ty}
  sets::AbstractVector{T}
  UnionSet(sets::AbstractVector{T}) where {T<:AbsSet} = 
    new{T, Union{eltype.(sets)...}}(sets)
end

# Accessors
###########

Base.iterate(e::UnionSet, i...) = iterate(e.sets, i...)

left(e::UnionSet) = first(e.sets)

right(e::UnionSet) = last(e.sets)

# ThSet implementation
######################

@instance ThSet{T} [model::UnionSet{SetOb, T}] where T begin

  contains(i::T)::Bool = any(s->i ∈ s, model.sets)

end

@instance ThFinSet{T} [model::UnionSet{FinSet, T}] where T begin

  contains(i::T)::Bool = any(s->i ∈ s, model.sets)

  length()::Int = length(iterator[model]())

  collect()::Vector{T} = union(collect.(model)...)

end

end # module
