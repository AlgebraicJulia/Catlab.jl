export AbsSet, SetOb

using StructEquality

using GATlab

import Base: eltype, contains

# Theory of Sets
################

"""
One ought be able to ask of any Set whether something is in it. Also a Julia 
type should be provided which includes all elements of the set.
"""
@theory ThSet begin
  Bool′::TYPE{Bool}
  Type′::TYPE{Type}
  contains(e::Type′)::Bool′ # the order of arguments is reversed, so give a diff name
  eltype()::Type′
end

""" There are two kinds of Abstract Set. `SetOb` and `FinSet`."""
abstract type AbsSet end

""" Fix the order of contains """
Base.in(x, s::AbsSet) = ThSet.contains[getvalue(s)](x)

# Wrapper type for Models of ThSet
##################################
"""
Generic type for a set. It has some implementation of the theory of sets and 
a model which provides the information for how it implements the theory.
"""
ThSet.Meta.@wrapper SetOb <: AbsSet

Base.show(io::IO, s::SetOb) = show(io, getvalue(s))

