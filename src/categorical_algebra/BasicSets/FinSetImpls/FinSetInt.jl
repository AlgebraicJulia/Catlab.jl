module FSetInt 

export FinSetInt

using StructEquality

using GATlab
import GATlab: getvalue

using ..FinSets: FinSetImpl, ThFinSet
import ..FinSets: FinSet

"""
A set {1,2,...,n} represented by a single `Int`
"""
@struct_hash_equal struct FinSetInt <: FinSetImpl
  n::Int
end 

# Accessor
###########

getvalue(f::FinSetInt) = f.n

# Other methods
###############

Base.show(io::IO, set::FinSetInt) = print(io, "FinSet($(set.n))")

# FinSet Implementation
#######################

@instance ThFinSet{Bool, Any, Int} [model::FinSetInt] begin
  in′(i::Any)::Bool = i isa Int && 0 < i ≤ getvalue(model)
  eltype′()::Any = Int
  length′()::Int = getvalue(model)
  iterate′()::Any = iterate(1:getvalue(model))
  iterate′(x::Any)::Any = iterate(1:getvalue(model), x)
end

""" Default model for a finset made out of a Julia `Int` """
FinSet(i::Int) = FinSet(FinSetInt(i))

""" Default FinSet with no parameters """
FinSet() = FinSet(0)

end # module