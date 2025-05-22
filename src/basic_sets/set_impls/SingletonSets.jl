module SingletonSets 

export SingletonSet

using StructEquality

using GATlab

using ..FinSets: ThFinSet
import ..FinSets: FinSet

""" A set with one element """
@struct_hash_equal struct SingletonSet end 


# Other methods
###############

Base.show(io::IO, ::SingletonSet) = print(io, "Singleton()")

# FinSet Implementation
#######################

@instance ThFinSet{Nothing} [model::SingletonSet] begin
  contains(::Nothing)::Bool = true
  length()::Int = 1
  collect()::Vector{Nothing} = [nothing]
end

""" Default model for a finset made out of a Julia `Int` """
FinSet(::Nothing) = FinSet(SingletonSet())

end # module
