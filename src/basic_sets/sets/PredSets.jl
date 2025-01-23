module PredSets 
export PredicatedSet

using ..Sets

# Predicated sets
#################

""" Set defined by a predicate (boolean-valued function) on a Julia data type.
"""
struct PredicatedSet{T} <: SetOb{T}
  predicate::Any

  PredicatedSet{T}(f) where T = new{T}(f)
end

PredicatedSet(T::Type, f) = PredicatedSet{T}(f)

function (s::PredicatedSet{T})(x::T)::Bool where {T}
  s.predicate(x)
end

function Base.show(io::IO, s::PredicatedSet{T}) where T
  print(io, "PredicatedSet($T, $(nameof(s.predicate)))")
end

end # module