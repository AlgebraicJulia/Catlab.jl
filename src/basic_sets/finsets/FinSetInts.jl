module FinSetInts 
export FinSetInt

using StructEquality

using ..FinSets 
import ..FinSets: FinSet

""" Finite set of the form ``{1,…,n}`` for some number ``n ≥ 0``.
"""
@struct_hash_equal struct FinSetInt <: FinSet{Int,Int}
  n::Int
end

FinSet{Int,Int}(n::Int) = FinSetInt(n) 
FinSet(n::Int) = FinSetInt(n)

Base.iterate(set::FinSetInt, args...) = iterate(1:set.n, args...)
Base.length(set::FinSetInt) = set.n
Base.in(elem, set::FinSetInt) = in(elem, 1:set.n)

Base.show(io::IO, set::FinSetInt) = print(io, "FinSet($(set.n))")

end # module