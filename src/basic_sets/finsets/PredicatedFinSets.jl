module PredFinSets 

export PredicatedFinSet

using StructEquality

using GATlab

using ..FinSets: FinSet, ThFinSet

""" Set defined by a predicate (boolean-valued function) on a Julia data type.
"""
@struct_hash_equal struct PredicatedFinSet{T}
  set::FinSet
  predicate::Any

  PredicatedFinSet{T}(f) where T = new{T}(f)
end

GATlab.getvalue(p::PredicatedFinSet) = p.set

PredicatedFinSet(T::Type, f) = PredicatedFinSet{T}(f)

# Other methods
###############


""" Apply the predicate """
function (s::PredicatedFinSet{T})(x::T)::Bool where {T}
  s.predicate(x)
end

function Base.show(io::IO, s::PredicatedFinSet{T}) where T
  print(io, "PredicatedFinSet($T, $(nameof(s.predicate)))")
end

# ThSet implementation 
######################

@instance ThFinSet [model::PredicatedFinSet{T}] where T begin

  contains(i::Any)::Bool = i in getvalue(model) && model(i)

  eltype()::Any = T

  length()::Int = length(collect(model))

  iterator()::Any = filter(contains[model], getvalue(model))

end

end # module
