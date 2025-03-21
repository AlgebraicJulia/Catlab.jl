module ProdSets 

export ProdSet, product

using StructEquality, MLStyle

using GATlab

import ....Theories: product
using ..BasicSets: ThSet, ThFinSet, AbsSet, SetOb, FinSet


""" 
Unbiased Cartesian product.
"""
@struct_hash_equal struct ProdSet{T<:AbsSet}
  sets::Vector{T}
end

GATlab.getvalue(s::ProdSet) = s.sets

# Other methods
###############

Base.iterate(e::ProdSet, i...) = iterate(getvalue(e), i...)

Base.getindex(e::ProdSet, i) = getvalue(e)[i]

Base.length(e::ProdSet) = length(getvalue(e))

# ThSet implementation
######################

contains_set(model::ProdSet, i) = 
  (i isa Tuple && length(i)==length(model) 

&& all(e ∈ s for (s, e) in zip(model, i)))

@instance ThSet [model::ProdSet{SetOb}] begin

  contains(i::Any)::Bool = contains_set(model, i)

  eltype()::Any = Tuple{eltype.(model)...}

end

@instance ThFinSet [model::ProdSet{FinSet}] begin

  contains(i::Any)::Bool = contains_set(model, i)

  eltype()::Any = Tuple{eltype.(model)...}

  length()::Int = prod(length.(model))

  iterator()::Any = Iterators.product(model...)

end

# constructors
###############

product(xs::SetOb...) = SetOb(ProdSet(xs))
product(xs::FinSet...) = FinSet(ProdSet(xs))

end # module