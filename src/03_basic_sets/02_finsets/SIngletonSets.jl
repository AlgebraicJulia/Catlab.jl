module SingletonSets 

export SingletonSet

using StructEquality

using GATlab

using ..FinSets: ThFinSet
import ..FinSets: FinSet

""" A set with one element """
@struct_hash_equal struct SingletonSet
end 


# Other methods
###############

Base.show(io::IO, ::SingletonSet) = print(io, "Singleton()")

# FinSet Implementation
#######################

@instance ThFinSet{Bool, Any, Int} [model::SingletonSet] begin
  in′(i::Any)::Bool = isnothing(i)
  eltype()::Any = Nothing
  length()::Int = 1
  iterate()::Any = iterate([nothing])
  iterate(x::Any)::Any = iterate([nothing], x)
end

""" Default model for a finset made out of a Julia `Int` """
FinSet(::Nothing) = FinSet(SingletonSet())

end # module
