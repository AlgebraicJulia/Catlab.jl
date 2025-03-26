module FinSets
export FinSet, AbsSet, ThFinSet, UnitRangeLike

using GATlab
using ..Sets: ThSet, SetOb
import Base: length, iterate

# Theory of FinSets
###################

"""
Any finite set must satisfy the interface of `ThSet` in addition to providing 
something which implements Julia's iterator interface and having a integer 
cardinality, i.e. `length`.
"""
@theory ThFinSet <: ThSet begin
  Int′::TYPE{Int}
  Any′::TYPE{Any}
  length()::Int′
  iterator()::Any′
end

# Wrapper type for Models of ThFinSet
#####################################

""" Finite set. """
ThFinSet.Meta.@wrapper FinSet

const AbsSet = Union{FinSet, SetOb}

# We shouldn't have this - TODO fix code that breaks when this is removed
FinSet(f::FinSet) = f 

Base.show(io::IO, set::FinSet) = show(io, getvalue(set))

Base.show(io::IO, mime::MIME"text/plain", set::AbsSet) = 
  show(io, mime, getvalue(set))

Base.show(io::IO, mime::MIME"text/html", set::AbsSet) = 
  show(io, mime, getvalue(set))

Base.iterate(f::FinSet, xs...) = iterate(ThFinSet.iterator(f), xs...)

Base.in(x, set::AbsSet) = try 
  ThFinSet.contains(set, x)
catch e 
  e isa MethodError || throw(e)
  false
end

Base.eltype(set::AbsSet)::Type = impl_type(set, :X)

""" For implementations of ThFinSet which are like 1:n """
abstract type UnitRangeLike end

end # module
