module SumFinSets 

export SumFinSet, TaggedElem

using StructEquality, MLStyle

using GATlab

using ..Sets: TaggedElem, Tagged, SetOb
import ..Sets: SumSet

using ..FinSets: ThFinSet, FinSetAsSet
import ..FinSets: FinSet


""" 
Unbiased disjoint union type. In order to not conflate values, we need to wrap 
them in `TaggedElem` which adds an integer type parameter.
"""
@struct_hash_equal struct SumFinSet
  sets::Vector{FinSet}
end

SumSet(sets::Vector{FinSet}) = SumFinSet(sets)

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

  # reuse implementation defined for `SumSet` by casting to a `SumSet`
  contains(i::Any)::Bool = ThFinSet.contains[SumSet(SetOb.(model))](i)

  eltype()::Any = Tagged(eltype.(model))

  length()::Int = sum(length.(model))

  iterator()::Any = it(model)
  
end

it(model) = Iterators.flatten(map(enumerate(model)) do (i, xs)
  map(xs) do x 
    TaggedElem(x, i)
  end
end)


end # module