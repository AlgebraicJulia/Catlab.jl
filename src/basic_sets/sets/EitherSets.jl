module EitherSets 

export EitherSet, Left, Right, either

using StructEquality

using GATlab

using ..Sets: ThSet, AbsSet, SetOb
import ..UnionSets: left, right

# Should this really be exported by GATlab?
# @struct_hash_equal struct Left{T}
#   val::T
# end
# @struct_hash_equal struct Right{S}
#   val::S
# end

GATlab.getvalue(l::Left) = l.val
GATlab.getvalue(r::Right) = r.val

Base.isless(x::Left, y::Left) = isless(getvalue(x), getvalue(y))

Base.isless(x::Right, y::Right) = isless(getvalue(x), getvalue(y))


""" 
Disjoint union type. In order to not conflate values, we need to wrap one 
of the sets in `Left` and one in `Right`. 
"""
@struct_hash_equal struct EitherSet
  left::AbsSet
  right::AbsSet
end

# Accessors
###########

left(e::EitherSet) = e.left

right(e::EitherSet) = e.right

# ThSet implementation
######################

@instance ThSet [model::EitherSet] begin

  in′(i::Any)::Bool = if i isa Left 
    getvalue(i) ∈ left(model) 
  elseif i isa Right 
    getvalue(i) ∈ right(model)
  else 
    false 
  end

  eltype()::Any = 
    Union{Left{eltype(left(model))}, Right{eltype(right(model))}}

end

# Constructors
##############

either(a::AbsSet, b::AbsSet) = 
  SetOb(EitherSet(a,b))

end # module