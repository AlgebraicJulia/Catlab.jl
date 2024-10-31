
# FinSetHash
#-----------

"""
A Julia finite set.
"""
@struct_hash_equal struct FinSetHash{T} <: FinSetImpl
  set::Set{T}
end 

getvalue(f::FinSetHash) = f.set

function Base.show(io::IO, set::FinSetHash)
  print(io, "FinSet(")
  show(io, set.set)
  print(io, ")")
end

@instance ThFinSet{Bool, Any, Int} [model::FinSetHash{T}] where T begin
  in′(i::Any)::Bool = i ∈ getvalue(model)
  eltype′() = T
  length′()::Int = length(getvalue(model))
  iterate′()::Any = iterate(getvalue(model))
  iterate′(x::Any)::Any = iterate(getvalue(model), x)
end

""" Default model for a finset made out of a Julia `Set` """
FinSet(s::Set{T}) where T = FinSet(FinSetHash(s))