""" Raw Julia type considered as a set"""
@struct_hash_equal struct TypeSet{T} <: SetImpl end

TypeSet(T::Type) = TypeSet{T}()

Base.show(io::IO, ::TypeSet{T}) where T = print(io, "TypeSet($T)")

# ThSet implementation 

@instance ThSet′{Bool, Any} [model::TypeSet{T}] where T begin
  in′(i::Any)::Bool = i isa T
  eltype′()::Any = T
end

# Default models

""" Default model for a Set made out of a Julia `Type` """
SetOb(T::Type) = SetOb(TypeSet{T}())