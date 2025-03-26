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
  length()::Int = length(iterator[model]())
  iterator()::Any = instances(T)
end

FinSet(::Type{T}) where {T<:Enum} = FinSet(EnumSet{T}())

end # module