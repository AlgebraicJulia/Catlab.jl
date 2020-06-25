""" Computing in the category of finite sets and relations, and its skeleton.
"""
module FinRelations
export BoolRig, RelationMatrix

import Base: +, *, zero, one
using AutoHashEquals

using ..Matrices

""" The rig of booleans.

This struct is needed because in base Julia, the product of booleans is another
boolean, but a sum of booleans is coerced to an integer: `true + true == 2`.
"""
@auto_hash_equals struct BoolRig
  value::Bool
end
+(x::BoolRig, y::BoolRig) = x.value || y.value
*(x::BoolRig, y::BoolRig) = x.value && y.value
zero(::Type{BoolRig}) = false
one(::Type{BoolRig}) = true

""" A relation matrix, also known as a boolean matrix or logical matrix.
"""
const RelationMatrix = AbstractMatrix{BoolRig}

end
