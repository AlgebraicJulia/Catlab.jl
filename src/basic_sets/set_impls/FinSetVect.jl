module FSetVect 

export FinSetVect

using StructEquality

using GATlab

using ..FinSets: ThFinSet
import ..FinSets: FinSet

""" Wrapper around a Julia `Vector`. """
@struct_hash_equal struct FinSetVect{T}
  vect::AbstractVector{T}
  function FinSetVect(v::AbstractVector{T}) where T 
    new{T}(unique(v)) # remove duplicates
  end
end 

# Accessor
###########

GATlab.getvalue(f::FinSetVect) = f.vect

function Base.show(io::IO, set::FinSetVect)
  print(io, "FinSet(")
  show(io, getvalue(set))
  print(io, ")")
end

# FinSet Implementation
#######################

@instance ThFinSet{T} [model::FinSetVect{T}] where T begin
  contains(i::T)::Bool = i ∈ getvalue(model)
  length()::Int = length(getvalue(model))
  collect()::AbstractVector{T} = getvalue(model)
end

""" Default model for a finset made out of a Julia `Set` """
FinSet(s::AbstractVector) = FinSet(FinSetVect(s))

end # module
