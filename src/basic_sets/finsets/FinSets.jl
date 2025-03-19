export FinSet

using GATlab
import GATlab: getvalue
using StructEquality

using ..Sets
using ..Sets: ThSet
import ..Sets: SetOb, left, right

import ....Theories: Ob
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

FinSet(set::FinSet) = set # no-op

Base.show(io::IO, set::FinSet) = show(io, getvalue(set))

Base.show(io::IO, mime::MIME"text/plain", set::FinSet) = 
  show(io, mime, getvalue(set))

Base.show(io::IO, mime::MIME"text/html", set::FinSet) = 
  show(io, mime, getvalue(set))

Base.iterate(f::FinSet, xs...) = iterate(ThFinSet.iterator(f), xs...)

Base.in(x, set::FinSet) = ThFinSet.contains(set, x)
