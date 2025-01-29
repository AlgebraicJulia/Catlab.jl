module SumSets 

export SumSet, NamedSumSet, TaggedElem, Tagged, untag, getidx, force, tag_T

using StructEquality, MLStyle

using GATlab

using ..Sets: ThSet′, AbsSet

""" An element tagged by an integer """
@struct_hash_equal struct TaggedElem{I, T} 
  val::T
  tag::I
  TaggedElem(t::T, tag) where T = new{Val{tag}, T}(t, Val(tag))

  TaggedElem{U}(t::T, tag) where {U,T<:U} = new{Val{tag}, U}(t, Val(tag))
end 

""" Coerce 

Needed for union types: we can't tell that a `Tagged{1, Bool}` is a 
`Tagged{1, Union{Bool, String}}`
"""
TaggedElem{I, T}(v::TaggedElem{I, K}) where {I,T, K<:T} = 
  TaggedElem{T}(getvalue(v), gettag(v))

GATlab.getvalue(l::TaggedElem) = l.val

GATlab.gettag(l::TaggedElem) = only(typeof(l.tag).parameters)

tag_T(::Type{TaggedElem{I,T}}) where {I,T} = T
tag_T(::TaggedElem{I,T}) where {I,T} = T

""" Untag at the term level """
untag(l::TaggedElem{I,T}, i::Int) where {I,T} =
  Val{i} == I  ? l.val : error("Bad untag of $(l.val)::$T: $I ≠ $i")

""" Untag at the type level """
untag(::Type{TaggedElem{I,T}}, i::Int) where {I,T} = 
  Val{i} == I ? T :  error("Bad untag of $T: $I ≠ $i")

""" Untag at the type level """
function untag(::Type{Union{Xs}}, i::Int) where Xs 
  Xs.a <: TaggedElem || error("Can't untag a $(Xs.a)")
  Xs.a.tag == i && return tag_T(Xs.a)
  return untag(Xs.b, i) # iterate through list of union types
end

getidx(::T) where {T<:TaggedElem} = only(T.parameters[1].parameters)

force(t::TaggedElem) = TaggedElem(force(getvalue(t)), gettag(t))

##########
# SumSet #
##########

""" 
Unbiased disjoint union type. In order to not conflate values, we need to wrap 
them in `TaggedElem` which adds an integer type parameter.
"""
@struct_hash_equal struct SumSet
  sets::Vector{AbsSet}
end

GATlab.getvalue(s::SumSet) = s.sets

# Other methods
###############

Base.iterate(e::SumSet, i...) = iterate(getvalue(e), i...)

Base.getindex(e::SumSet, i) = getvalue(e)[i]

Base.length(e::SumSet) = length(getvalue(e))

# ThSet implementation
######################

@instance ThSet′ [model::SumSet] begin

  in′(i::Any)::Bool = @match i begin 
    (t::TaggedElem) => let i = getidx(t); 
      0 < i ≤ length(model) && getvalue(t) ∈ model[i]
    end
    _ => false 
  end

  eltype()::Any = Tagged(eltype.(model))
end

# Other helpers
###############
Tagged(vs::Vector{<:Union{Type,TypeVar}}) = 
  Union{[TaggedElem{Val{i}, v} for (i,v) in zip(1:length(vs), vs)]...}

###############
# NamedSumSet #
###############

""" 
Unbiased disjoint union type. In order to not conflate values, we need to wrap 
them in `TaggedElem` which adds an integer type parameter.
"""
@struct_hash_equal struct NamedSumSet
  sets::Dict{Any, AbsSet}
end

GATlab.getvalue(s::NamedSumSet) = s.sets

# Other methods
###############

Base.iterate(e::NamedSumSet, i...) = iterate(getvalue(e), i...)

Base.getindex(e::NamedSumSet, i) = getvalue(e)[i]

Base.length(e::NamedSumSet) = length(getvalue(e))

Base.haskey(e::NamedSumSet, k) = haskey(getvalue(e), k)

# ThSet implementation
######################

@instance ThSet′ [model::NamedSumSet] begin

  in′(i::Any)::Bool = @match i begin 
    (t::TaggedElem) => let i = getidx(t); 
      haskey(model, i) && getvalue(t) ∈ model[i]
    end
    _ => false 
  end

  eltype()::Any = Tagged(Dict(k=>eltype(v) for (k,v) in getvalue(model)))

end

# Other helpers
###############
Tagged(vs::Dict{<:Any, <:Union{Type,TypeVar}}) = 
  Union{[TaggedElem{Val{i}, v} for (i,v) in pairs(vs)]...}


end # module
