module Sets 

export SetOb, ThSet

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
  X::TYPE
  Bool′::TYPE{Bool}
  contains(e::X)::Bool′
end

# Wrapper type for Models of ThSet
##################################
"""
Generic type for a set. It has some implementation of the theory of sets and 
a model which provides the information for how it implements the theory.
"""
ThSet.Meta.@wrapper SetOb

Base.show(io::IO, set::SetOb) = show(io, getvalue(set))

end # module