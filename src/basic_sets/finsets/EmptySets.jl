module EmptySets 

export EmptySet

using StructEquality

using GATlab

using ..FinSets: ThFinSet
import ..FinSets: FinSet

""" A set with no elements """
@struct_hash_equal struct EmptySet end 

# Other methods
###############

Base.show(io::IO, ::EmptySet) = print(io, "Empty()")

# FinSet Implementation
#######################

@instance ThFinSet [model::EmptySet] begin
  in′(i::Any)::Bool = false
  eltype()::Any = Union{}
  length()::Int = 0
  iterator()::Any = Union{}[]
end

end # module
