module FinSetInts

export FinSetInt

using StructEquality

using GATlab

using ..FinSets:ThFinSet
import ..FinSets: FinSet

"""
A set {1,2,...,n} represented by a single `Int`
"""
@struct_hash_equal struct FinSetInt
  n::Int
end 

# Accessor
###########

GATlab.getvalue(f::FinSetInt) = f.n

# Other methods
###############

Base.show(io::IO, set::FinSetInt) = print(io, "FinSet($(set.n))")
Base.show(io::IO, ::MIME"text/html", set::FinSetInt) = show(io, set)

Base.length(f::FinSetInt) = getvalue(f)

Base.iterate(f::FinSetInt, xs...) = iterate(1:getvalue(f), xs...)

Base.eltype(::FinSetInt) = Int

# FinSet Implementation
#######################

@instance ThFinSet [model::FinSetInt] begin
  in′(i::Any)::Bool = i isa Int && 0 < i ≤ getvalue(model)
  eltype()::Any = Int
  length()::Int = getvalue(model)
  iterator()::Any = 1:getvalue(model)
end

""" Default model for a finset made out of a Julia `Int` """
FinSet(i::Int) = FinSet(FinSetInt(i))

""" Default FinSet with no parameters """
FinSet() = FinSet(0)

end # module
