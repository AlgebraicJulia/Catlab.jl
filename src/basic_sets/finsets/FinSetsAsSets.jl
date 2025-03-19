module FinSetsAsSets

export FinSetAsSet 

using StructEquality
using GATlab 
using ..FinSets: FinSet, ProdFinSet
using ...Sets: ThSet, ProdSet
import ...Sets: SetOb

""" 
Interpret a FinSet as a Set. This can be alternatively handled by doing a Δ
migration along the inclusion of theories ThSet ↣ ThFinSet
"""
@struct_hash_equal struct FinSetAsSet 
  val::FinSet
end 

GATlab.getvalue(f::FinSetAsSet) = f.val

@instance ThSet [model::FinSetAsSet] begin 
  contains(i::Any) = contains(getvalue(model), i)
  eltype()::Type = eltype(getvalue(model))
end

SetOb(f::FinSet) = SetOb(FinSetAsSet(f))

SetOb(::Nothing) = SetOb(FinSet(nothing))

SetOb(i::Int) = SetOb(FinSet(i))

Base.length(s::SetOb) = length(FinSet(s))

Base.iterate(s::SetOb, xs...) = iterate(FinSet(s), xs...)

function FinSet(s::SetOb)
  i = getvalue(s)
  i isa FinSetAsSet && return getvalue(i)
  i isa ProdSet && return FinSet(ProdFinSet(i))
  error("Cannot convert SetOb $s into a FinSet")
end

end # module
