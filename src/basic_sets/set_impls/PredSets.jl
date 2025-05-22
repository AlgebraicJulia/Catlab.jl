module PredSets 

export PredicatedSet

using StructEquality

using GATlab

using ..BasicSets: SetOb, ThSet, ThFinSet, AbsSet, FinSet

""" Set defined by a predicate (boolean-valued function) on a Julia data type.
"""
@struct_hash_equal struct PredicatedSet{T<:AbsSet, El}
  set::T
  predicate::Any

  PredicatedSet(set::T,f) where {T<:AbsSet} = new{T, eltype(set)}(set, f)
end

PredicatedSet(T::Type, f) = PredicatedSet(SetOb(T), f)

# Other methods
###############

GATlab.getvalue(p::PredicatedSet) = p.set


""" Apply the predicate """
(s::PredicatedSet)(x::Any)::Bool = s.predicate(x)

function Base.show(io::IO, s::PredicatedSet)
  print(io, "PredicatedSet($(getvalue(s.set)), $(nameof(s.predicate)))")
end

# ThSet implementation 
######################

@instance ThSet{T} [model::PredicatedSet{SetOb, T}] where T begin

  contains(i::T)::Bool = i ∈ getvalue(model) && model(i)

end


@instance ThFinSet{T} [model::PredicatedSet{FinSet, T}] where T begin

  contains(i::T)::Bool = i ∈ getvalue(model) && model(i)

  length()::Int = length(collect(model))

  collect()::Vector{T} = filter(contains[model], getvalue(model))

end

end # module
