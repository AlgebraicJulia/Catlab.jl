module EitherSets 

export EitherSet, Left, Right

using StructEquality

using GATlab
import GATlab: getvalue

using ..Sets: SetImpl, ThSet′, AbsSet
import ..UnionSets: left, right


""" Wrapper defined in GATlab """
getvalue(l::Left) = l.val 

""" Wrapper defined in GATlab"""
getvalue(l::Right) = l.val 

""" 
Disjoint union type. In order to not conflate values, we need to wrap one 
of the sets in `Left` and one in `Right`. 
"""
@struct_hash_equal struct EitherSet <: SetImpl
  left::AbsSet
  right::AbsSet
end

# Accessors
###########

left(e::EitherSet) = e.left

right(e::EitherSet) = e.right

# ThSet implementation
######################

@instance ThSet′{Bool, Any} [model::EitherSet] begin

  in′(i::Any)::Bool = if i isa Left 
    getvalue(i) ∈ left(model) 
  elseif i isa Right 
    getvalue(i) ∈ right(model)
  else 
    false 
  end

  eltype′()::Any = 
    Union{Left{eltype(left(model))}, Right{eltype(right(model))}}

end


end # module