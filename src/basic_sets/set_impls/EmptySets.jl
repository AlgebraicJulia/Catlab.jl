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

@instance ThFinSet{Union{}} [model::EmptySet] begin
  contains(::Union{})::Bool = false
  length()::Int = 0
  collect()::Vector{Union{}} = Union{}[]
end

end # module
