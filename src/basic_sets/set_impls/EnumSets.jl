module EnumSets 

using GATlab 

using ..FinSets: ThFinSet
using .ThFinSet

# Do we need a wrapper type EnumSet or can Enums directly be a model?

@instance ThFinSet [model::Enum] begin
  contains(i::Any)::Bool = i isa model
  eltype()::Type = model
  length()::Int = length(iterator[model]())
  iterator()::Any = instances(model)
end

end # module