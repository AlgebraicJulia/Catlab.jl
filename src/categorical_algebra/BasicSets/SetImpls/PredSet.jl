
# Predicated sets
#----------------

""" Set defined by a predicate (boolean-valued function) on a Julia data type.
"""
@struct_hash_equal struct PredicatedSet{T} <: SetImpl
  predicate::Any

  PredicatedSet{T}(f) where T = new{T}(f)
end

PredicatedSet(T::Type, f) = PredicatedSet{T}(f)

""" Apply the predicate """
function (s::PredicatedSet{T})(x::T)::Bool where {T}
  s.predicate(x)
end

function Base.show(io::IO, s::PredicatedSet{T}) where T
  print(io, "PredicatedSet($T, $(nameof(s.predicate)))")
end

# ThSet implementation 
@instance ThSet′{Bool, Any} [model::PredicatedSet{T}] where T begin
  in′(i::Any)::Bool = i isa T && model(i)
  eltype′()::Any = T
end