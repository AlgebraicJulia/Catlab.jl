module TypeSets 

export TypeSet

using StructEquality

using GATlab

using ..Sets: ThSet′
import ..Sets: SetOb

""" Raw Julia type considered as a set"""
@struct_hash_equal struct TypeSet{T} end

TypeSet(T::Type) = TypeSet{T}()

Base.show(io::IO, ::TypeSet{T}) where T = print(io, "TypeSet($T)")

# ThSet implementation 

@instance ThSet′{Bool, Any} [model::TypeSet{T}] where T begin
  in′(i::Any)::Bool = i isa T
  eltype()::Any = T
end

# Default model, for convenience

""" Default model for a Set made out of a Julia `Type` """
SetOb(T::Type) = SetOb(TypeSet{T}())

end # module