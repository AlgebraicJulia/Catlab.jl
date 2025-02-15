
module ProdFinSets 

export ProdFinSet

using StructEquality

using GATlab

using ..Sets: ProdSet
using ..FinSets: ThFinSet
import ..FinSets: FinSet


""" 
Unbiased Cartesian product of finite sets.
"""
@struct_hash_equal struct ProdFinSet
  sets::Vector{FinSet}
end

GATlab.getvalue(p::ProdFinSet) = p.sets

""" Assuming all sets are finite in a `ProdSet`, convert to `ProdFinSet` """
FinSet(s::ProdSet) = FinSet(ProdFinSet(getvalue(s)))

""" Relax assumption that all sets are finite """
ProdSet(f::ProdFinSet) = ProdSet(getvalue(f))

# Other methods
###############

Base.iterate(e::ProdFinSet, i...) = iterate(getvalue(e), i...)

Base.getindex(e::ProdFinSet, i) = getvalue(e)[i]

Base.length(e::ProdFinSet) = length(getvalue(e))

# ThSet implementation
######################

@instance ThFinSet [model::ProdFinSet] begin

  in′(i::Any)::Bool = ThFinSet.in′[ProdSet(model)](i) # reuse implementation

  eltype()::Any = Tuple{eltype.(model)...}

  length()::Int = prod(length.(model))

  iterator()::Any = Iterators.product(model...)

end

end # module
