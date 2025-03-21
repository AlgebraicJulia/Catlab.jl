export SetOb

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

# Wrapper type for Models of ThSet
##################################
"""
Generic type for a set. It has some implementation of the theory of sets and 
a model which provides the information for how it implements the theory.
"""
ThSet.Meta.@wrapper SetOb

Base.show(io::IO, s::SetOb) = show(io, getvalue(s))

""" Fix the order of contains """
Base.in(x, s::SetOb) = ThSet.contains[getvalue(s)](x)
