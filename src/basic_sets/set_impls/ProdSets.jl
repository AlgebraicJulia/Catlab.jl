module ProdSets 

export ProdSet, product

using StructEquality
using GATlab

import ....Theories: product
using ..BasicSets: ThSet, ThFinSet, AbsSet, SetOb, FinSet


""" 
Unbiased Cartesian product.
"""
@struct_hash_equal struct ProdSet{T<:AbsSet, El}
  sets::Vector{T}
  ProdSet(sets::Vector{T}) where {T<:AbsSet} = 
    new{T, Tuple{eltype.(sets)...}}(sets)
end

GATlab.getvalue(s::ProdSet) = s.sets

# Other methods
###############

Base.iterate(e::ProdSet, i...) = iterate(getvalue(e), i...)

Base.getindex(e::ProdSet, i) = getvalue(e)[i]

Base.length(e::ProdSet) = length(getvalue(e))

# ThSet implementation
######################

# common to ThSet and ThFinSet implementations
contains_set(model::ProdSet, i) = all(e ∈ s for (s, e) in zip(model, i))

@instance ThSet{T} [model::ProdSet{SetOb,T}] where T begin

  contains(i::T)::Bool = contains_set(model, i)

end

@instance ThFinSet{T} [model::ProdSet{FinSet,T}] where T begin

  contains(i::T)::Bool = contains_set(model, i)

  length()::Int = prod(length.(model); init=1)

  collect()::AbstractVector{T} = vec(collect(Iterators.product(model...)))

end

# constructors
###############

product(xs::SetOb...) = SetOb(ProdSet(xs))
product(xs::FinSet...) = FinSet(ProdSet(xs))

end # module