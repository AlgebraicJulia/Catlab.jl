module FSetHash 

export FinSetHash

using StructEquality

using GATlab
import GATlab: getvalue

using ..FinSets: ThFinSet
import ..FinSets: FinSet

""" Wrapper around a Julia `Set`. """
@struct_hash_equal struct FinSetHash{T} 
  set::Set{T}
end 

# Accessor
###########

getvalue(f::FinSetHash) = f.set

function Base.show(io::IO, set::FinSetHash)
  print(io, "FinSet(")
  show(io, set.set)
  print(io, ")")
end

# FinSet Implementation
#######################

@instance ThFinSet [model::FinSetHash{T}] where T begin
  in′(i::Any)::Bool = i ∈ getvalue(model)
  eltype() = T
  length()::Int = length(getvalue(model))
  iterate()::Any = iterate(getvalue(model))
  iterate(x::Any)::Any = iterate(getvalue(model), x)
end

""" Default model for a finset made out of a Julia `Set` """
FinSet(s::Set{T}) where T = FinSet(FinSetHash(s))

end # module
