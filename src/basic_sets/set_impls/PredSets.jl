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

@instance ThSet [model::PredicatedSet{SetOb, T}] where T begin

  contains(i::Any)::Bool = i ∈ getvalue(model) && model(i)

  eltype()::Any = T

end


@instance ThFinSet [model::PredicatedSet{FinSet}] begin

  contains(i::Any)::Bool = i ∈ getvalue(model) && model(i)

  eltype()::Any = T

  length()::Int = length(collect(model))

  iterator()::Any = filter(contains[model], getvalue(model))

end

end # module
