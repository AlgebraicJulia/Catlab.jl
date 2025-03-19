module ProdSets 

export ProdSet, product

using StructEquality, MLStyle

using GATlab

import ....Theories: product
using ..Sets: ThSet, SetOb


""" 
Unbiased Cartesian product.
"""
@struct_hash_equal struct ProdSet
  sets::Vector{SetOb}
end

GATlab.getvalue(s::ProdSet) = s.sets

# Other methods
###############

Base.iterate(e::ProdSet, i...) = iterate(getvalue(e), i...)

Base.getindex(e::ProdSet, i) = getvalue(e)[i]

Base.length(e::ProdSet) = length(getvalue(e))

# ThSet implementation
######################

@instance ThSet [model::ProdSet] begin

  contains(i::Any)::Bool = (i isa Tuple && length(i)==length(model) 
    && all(e ∈ s for (s, e) in zip(model, i)))

  eltype()::Any = Tuple{eltype.(model)...}

end

# constructors
###############

product(xs::SetOb...) = SetOb(ProdSet(xs))

end # module