module TypeSets 

export TypeSet

using StructEquality
using GATlab

using ..Sets: ThSet
import ..Sets: SetOb

""" Raw Julia type, considered as a set"""
@struct_hash_equal struct TypeSet{T} end

GATlab.getvalue(::TypeSet{T}) where T = T

TypeSet(T::Type) = TypeSet{T}()

Base.show(io::IO, ::TypeSet{T}) where T = print(io, "TypeSet($T)")

# ThSet implementation 
######################

@instance ThSet{T} [model::TypeSet{T}] where T begin
  contains(i::T)::Bool = true
end

# Default model, for convenience
################################

""" Default model for a Set made out of a Julia `Type` """
SetOb(T::Type) = SetOb(TypeSet{T}())

end # module
