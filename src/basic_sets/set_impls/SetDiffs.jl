module SetDiffs 

export SetDiff

using StructEquality
using GATlab

using ..BasicSets: ThSet, ThFinSet, AbsSet, SetOb, FinSet


""" 
A set difference, A ∖ B
"""
@struct_hash_equal struct SetDiff{T<:AbsSet, El}
  val::T
  diff::AbsSet
  SetDiff(val::T, diff::AbsSet) where {T<:AbsSet} =
    new{T, eltype(val)}(val, diff)
end

GATlab.getvalue(e::SetDiff) = e.val

# ThSet implementation
######################

# common to ThSet and ThFinSet implementations
contains_set(model::SetDiff, i) = i ∉ model.diff && i ∈ getvalue(model)

@instance ThSet{T} [model::SetDiff{SetOb,T}] where T begin
  contains(i::T)::Bool = contains_set(model, i)
end

@instance ThFinSet{T} [model::SetDiff{FinSet,T}] where T begin

  contains(i::T)::Bool = contains_set(model, i)

  length()::Int = length(collect[model]())

  collect()::AbstractVector{T} = filter(∉(model.diff), collect(getvalue(model)))

end

end # module