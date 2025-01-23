module Cats 

using Reexport

include("Categories.jl")
@reexport using .Categories

include("FinCats.jl")
@reexport using .FinCats

include("FreeDiagrams.jl")
@reexport using .FreeDiagrams

include("Limits.jl")
@reexport using .Limits

include("Diagrams.jl")
@reexport using .Diagrams

include("DiscreteCats.jl")
@reexport using .DiscreteCats

include("GraphCategories.jl")

include("CommutativeDiagrams.jl")
@reexport using .CommutativeDiagrams

include("SliceCategories.jl")
@reexport using .SliceCategories

include("Subobjects.jl")
@reexport using .Subobjects

end # module
