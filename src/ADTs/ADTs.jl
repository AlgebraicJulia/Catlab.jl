module ADTs 

using Reexport

include("ADTsCore.jl")
include("RelationTerm.jl")

@reexport using .ADTsCore
@reexport using .RelationTerm

end