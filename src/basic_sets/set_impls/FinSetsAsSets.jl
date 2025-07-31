module FinSetsAsSets

export FinSetAsSet 

using StructEquality
using GATlab 
using ..BasicSets: ThSet, FinSet, ThFinSet
using ..ProdSets: ProdSet
import ..Sets: SetOb

""" 
Interpret a FinSet as a Set. This can be alternatively handled by doing a Δ
migration along the inclusion of theories ThSet ↣ ThFinSet
"""
@struct_hash_equal struct FinSetAsSet{T}
  val::FinSet
  FinSetAsSet(f::FinSet) = new{eltype(f)}(f)
end 

GATlab.getvalue(f::FinSetAsSet) = f.val

@instance ThSet{T} [model::FinSetAsSet{T}] where T begin 
  contains(i::T) = contains(getvalue(model), i)
end

SetOb(f::FinSet) = SetOb(FinSetAsSet(f))

SetOb(::Nothing) = SetOb(FinSet(nothing))

SetOb(i::Int) = SetOb(FinSet(i))

Base.length(s::SetOb) = length(FinSet(s))

Base.iterate(s::SetOb, xs...) = iterate(FinSet(s), xs...)

function FinSet(s::SetOb)
  i = getvalue(s)
  implements(i, ThFinSet) && return FinSet(i)
  i isa FinSetAsSet && return getvalue(i)
  i isa ProdSet && return FinSet(ProdSet(Vector{FinSet}(FinSet.(i))))
  error("Cannot convert SetOb $s into a FinSet")
end

FinSet(s::FinSetAsSet) = getvalue(s)

end # module
