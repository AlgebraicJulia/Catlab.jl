
module ProdFinSets 

export ProdFinSet

using StructEquality

using GATlab

using ..Sets: SetOb
using ..FinSets: ThFinSet
import ..FinSets: FinSet
import ..Sets: ProdSet


""" 
Unbiased Cartesian product of finite sets.
"""
@struct_hash_equal struct ProdFinSet
  sets::Vector{FinSet}
end

ProdSet(sets::Vector{FinSet}) = ProdFinSet(sets)

GATlab.getvalue(p::ProdFinSet) = p.sets

""" Assuming all sets are finite in a `ProdSet`, convert to `ProdFinSet` """
FinSet(s::ProdSet) = FinSet(ProdFinSet(getvalue(s)))

""" Relax assumption that all sets are finite """
ProdSet(f::ProdFinSet) = ProdSet(getvalue(f))

ProdFinSet(f::ProdSet) = ProdFinSet(FinSet.(f))

# Other methods
###############

Base.iterate(e::ProdFinSet, i...) = iterate(getvalue(e), i...)

Base.getindex(e::ProdFinSet, i) = getvalue(e)[i]

Base.length(e::ProdFinSet) = length(getvalue(e))

# ThSet implementation
######################

@instance ThFinSet [model::ProdFinSet] begin

  contains(i::Any)::Bool = ThFinSet.contains[ProdSet(SetOb.(model))](i) # reuse implementation

  eltype()::Any = Tuple{eltype.(model)...}

  length()::Int = prod(length.(model))

  iterator()::Any = Iterators.product(model...)

end

end # module
