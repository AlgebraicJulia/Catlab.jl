module ImgSets 

export ImgSet

using StructEquality
using GATlab

import ....Theories: product
using ..BasicSets: ThSet, ThFinSet, AbsSet, SetOb, FinSet, FinFunction, FinDomFunction, codom


""" 
Image of a (finite domain) function. Elements are in it iff there exists some element in the domain which is mapped onto it.
"""
@struct_hash_equal struct ImgSet{T<:AbsSet, El}
  img::Set{El}
  fun::Union{FinFunction, FinDomFunction}
  ImgSet(val::Union{FinFunction, FinDomFunction}) =
    new{typeof(codom(val)), eltype(codom(val))}(Set(collect(val)), val)
end

GATlab.getvalue(s::ImgSet) = s.img

# ThSet implementation
######################

@instance ThSet{T} [model::ImgSet{SetOb,T}] where T begin
  contains(i::T)::Bool = i ∈ getvalue(model)
end

@instance ThFinSet{T} [model::ImgSet{FinSet,T}] where T begin

  contains(i::T)::Bool = i ∈ getvalue(model)

  length()::Int = length(collect[model]())

  collect()::AbstractVector{T} = collect(getvalue(model))

end

end # module