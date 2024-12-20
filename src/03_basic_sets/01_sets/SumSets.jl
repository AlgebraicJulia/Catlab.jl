module SumSets 

export SumSet, TaggedElem

using StructEquality, MLStyle

using GATlab

using ..Sets: ThSet′, AbsSet


@struct_hash_equal struct TaggedElem{I, T} 
  val::T
  TaggedElem(t::T, i::Int) where T = new{Val{i}, T}(t)
end 

GATlab.getvalue(l::TaggedElem) = l.val 

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


end # module