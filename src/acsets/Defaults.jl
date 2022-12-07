module Defaults
export Default, default, isdefault, DefaultVal, DefaultEmpty

"""
This is a hack in order to pass in a default initializer for
[`DefaultVecMap`](@ref) as a type parameter
"""
abstract type Default end

struct DefaultVal{x} <: Default
end

default(::Type{DefaultVal{x}}) where {x} = x

struct DefaultEmpty{T} <: Default
end

default(::Type{DefaultEmpty{T}}) where {T} = T()

end
