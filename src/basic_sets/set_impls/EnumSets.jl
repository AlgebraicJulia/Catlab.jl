module EnumSets 
export EnumSet 

using StructEquality
using GATlab 

using ..FinSets: ThFinSet
import ..FinSets: FinSet
using .ThFinSet

@struct_hash_equal struct EnumSet{T<:Enum} end 

@instance ThFinSet{T} [model::EnumSet{T}] where T begin
  contains(i::T)::Bool = true
  length()::Int = length(instances(T))
  collect()::Vector{T} = collect(instances(T))
end

FinSet(::Type{T}) where {T<:Enum} = FinSet(EnumSet{T}())

end # module