module FinSets
export FinSet, AbsSet, ThFinSet, UnitRangeLike, coerce_setob, ≃

using GATlab
using ..Sets: ThSet, SetOb
import Base: length, collect

# Theory of FinSets
###################

"""
Any finite set must satisfy the interface of `ThSet` in addition to providing 
something which can result in a vector (of arbitrary order) and having a integer 
cardinality, i.e. `length`.

Morally, VX=Vector{X}. But this is a type dependent on a type, rather than on a 
term, so it is not expressible.
"""
@theory ThFinSet <: ThSet begin
  Int′::TYPE{Int}
  VX::TYPE{Any} 
  length()::Int′
  collect()::VX
end

# Wrapper type for Models of ThFinSet
#####################################

""" Finite set. """
ThFinSet.Meta.@wrapper FinSet

const AbsSet = Union{FinSet, SetOb}

""" Interpret an AbsSet as a SetOb """
coerce_setob(f::FinSet) = SetOb(getvalue(f))
coerce_setob(s::SetOb) = s

# We shouldn't have this - TODO fix code that breaks when this is removed
FinSet(f::FinSet) = f 

Base.show(io::IO, set::FinSet) = show(io, getvalue(set))

Base.show(io::IO, mime::MIME"text/plain", set::AbsSet) = 
  show(io, mime, getvalue(set))

Base.show(io::IO, mime::MIME"text/html", set::AbsSet) = 
  show(io, mime, getvalue(set))

Base.iterate(f::FinSet, xs...) = iterate(ThFinSet.collect(f), xs...)

Base.in(x, set::AbsSet) = try 
  ThFinSet.contains(set, x)
catch e 
  e isa MethodError || throw(e)
  false
end

Base.eltype(set::AbsSet)::Type = impl_type(set, :X)

""" For implementations of ThFinSet which are like 1:n """
abstract type UnitRangeLike end

""" Extensional equality """
≃(a::FinSet, b::FinSet) = a == b ? true : Set(collect(a)) == Set(collect(b))

""" Extensional equality: for (potentially) infinite sets, this is just equality because it can't actually be decided extensionally """
≃(a::AbsSet, b::AbsSet) = a == b

"""
Check whether a list of things are extensionally equivalent
"""
function ≃(as::Vector{T}, bs::Vector{T}) where T 
  length(as) == length(bs) || return false 
  all(((a,b),)-> a ≃ b, zip(as, bs))
end

end # module
