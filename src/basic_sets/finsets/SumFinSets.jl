module SumFinSets 

export SumFinSet, TaggedElem

using StructEquality, MLStyle

using GATlab

using ..Sets: TaggedElem
import ..Sets: SumSet

using ..FinSets: ThFinSet
import ..FinSets: FinSet


""" 
Unbiased disjoint union type. In order to not conflate values, we need to wrap 
them in `TaggedElem` which adds an integer type parameter.
"""
@struct_hash_equal struct SumFinSet
  sets::Vector{FinSet}
end

GATlab.getvalue(s::SumFinSet) = s.sets

FinSet(s::SumSet) = FinSet(SumFinSet(getvalue(s)))

SumSet(f::SumFinSet) = SumSet(getvalue(f))

# Other methods
###############

Base.iterate(e::SumFinSet, i...) = iterate(getvalue(e), i...)

Base.getindex(e::SumFinSet, i) = getvalue(e)[i]

Base.length(e::SumFinSet) = length(getvalue(e))

# ThSet implementation
######################

@instance ThFinSet [model::SumFinSet] begin

  in′(i::Any)::Bool = ThFinSet.in′[SumSet(model)](i) # reuse implementation

  eltype()::Any = ThFinSet.eltype[SumSet(model)]()

  length()::Int = sum(length.(model))

  iterate()::Any = iterate(it(model))

  iterate(x::Any)::Any = iterate(it(model), x)
  
end

it(model) = Iterators.flatten(map(enumerate(model)) do (i, xs)
  map(xs) do x 
    TaggedElem(x, i)
  end
end)


end # module