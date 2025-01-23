module TypeSets 
export TypeSet

using ..Sets

""" A Julia data type regarded as a set.
"""
struct TypeSet{T} <: SetOb{T} end

TypeSet(T::Type) = TypeSet{T}()

Base.show(io::IO, ::TypeSet{T}) where T = print(io, "TypeSet($T)")
Base.in(elem,::TypeSet{T}) where T = isa(elem,T)

end # module
