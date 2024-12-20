module Categories

using Reexport

include("Categories.jl")
include("TypeCats.jl")
include("OpCats.jl")
include("TrivialCats.jl")

@reexport using .TypeCats
@reexport using .OpCats
@reexport using .TrivialCats

end # module
