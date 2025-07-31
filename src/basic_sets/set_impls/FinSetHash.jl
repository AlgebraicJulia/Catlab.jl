module FSetHash 

export FinSetHash

using StructEquality

using GATlab

using ..FinSets: ThFinSet
import ..FinSets: FinSet

""" Wrapper around a Julia `Set`. """
@struct_hash_equal struct FinSetHash{T} 
  set::Set{T}
  FinSetHash(s::Set{T}) where T = T == Any ? error("here") : new{T}(s)
end 

# Accessor
###########

GATlab.getvalue(f::FinSetHash) = f.set

function Base.show(io::IO, set::FinSetHash)
  print(io, "FinSet(")
  show(io, set.set)
  print(io, ")")
end

# FinSet Implementation
#######################

@instance ThFinSet{T} [model::FinSetHash{T}] where T begin
  contains(i::T)::Bool = i ∈ getvalue(model)
  length()::Int = length(getvalue(model))
  collect()::Vector{T} = collect(getvalue(model))
end

""" Default model for a finset made out of a Julia `Set` """
FinSet(s::Set{T}) where T = FinSet(FinSetHash(s))

end # module
