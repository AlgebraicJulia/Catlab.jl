module SumSets 

export SumSet, TaggedElem, Tagged, untag, getidx

using StructEquality, MLStyle

using GATlab

using ..Sets: ThSet′, AbsSet


@struct_hash_equal struct TaggedElem{I, T} 
  val::T
  TaggedElem(t::T, i::Int) where T = new{Val{i}, T}(t)
end 

GATlab.getvalue(l::TaggedElem) = l.val

tag_I(::Type{TaggedElem{I,T}}) where {I,T} = I 
tag_T(::Type{TaggedElem{I,T}}) where {I,T} = T

""" Untag at the term level """
untag(l::TaggedElem{I,T}, i::Int) where {I,T} =
  Val{i} == I  ? l.val : error("Bad untag of $(l.val)::$T: $I ≠ $i")

""" Untag at the type level """
untag(::Type{TaggedElem{I,T}}, i::Int) where {I,T} = 
  Val{i} == I ? T :  error("Bad untag of $T: $I ≠ $i")

""" Untag at the type level """
function untag(::Type{Union{Xs}}, i::Int) where Xs 
  Xs.a <: TaggedElem || error("Can't untag a $(Xs.a)")
  tag_I(Xs.a) == Val{i} && return tag_T(Xs.a)
  return untag(Xs.b, i) # iterate through list of union types
end


getidx(::T) where {T<:TaggedElem} = only(T.parameters[1].parameters)

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

@instance ThSet′{Bool, Any} [model::SumSet] begin

  in′(i::Any)::Bool = @match i begin 
    (t::TaggedElem) => let i = getidx(t); 
      0 < i ≤ length(model) && getvalue(t) ∈ model[getidx(t)]
    end
    _ => false 
  end

  eltype()::Any = 
    Union{[TaggedElem{Val{i}, eltype(s)} for (i, s) in enumerate(model)]...}

end

# Other helpers
###############
Tagged(vs::Vector{<:Union{Type,TypeVar}}) = 
  Union{[TaggedElem{Val{i}, v} for (i,v) in zip(1:length(vs), vs)]...}


end # module