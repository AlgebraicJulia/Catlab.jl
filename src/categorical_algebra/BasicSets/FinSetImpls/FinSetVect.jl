module FSetVect 

export FinSetVect

using StructEquality

using GATlab
import GATlab: getvalue

using ..FinSets: FinSetImpl, ThFinSet
import ..FinSets: FinSet

""" Wrapper around a Julia `Vector`. """
@struct_hash_equal struct FinSetVect{T} <: FinSetImpl
  vect::AbstractVector{T}
  function FinSetVect(v::AbstractVector{T}) where T 
    new{T}(unique(v)) # remove duplicates
  end
end 

# Accessor
###########

getvalue(f::FinSetVect) = f.vect

function Base.show(io::IO, set::FinSetVect)
  print(io, "FinSet(")
  show(io, getvalue(set))
  print(io, ")")
end

# FinSet Implementation
#######################

@instance ThFinSet{Bool, Any, Int} [model::FinSetVect{T}] where T begin
  in′(i::Any)::Bool = i ∈ getvalue(model)
  eltype′() = T
  length′()::Int = length(getvalue(model))
  iterate′()::Any = iterate(getvalue(model))
  iterate′(x::Any)::Any = iterate(getvalue(model), x)
end

""" Default model for a finset made out of a Julia `Set` """
FinSet(s::AbstractVector{T}) where T = FinSet(FinSetVect(s))

end # module