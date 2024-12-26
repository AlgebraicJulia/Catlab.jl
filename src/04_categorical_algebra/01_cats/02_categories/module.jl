module Categories

using Reexport

include("Categories.jl")
include("TypeCats.jl")
include("OpCats.jl")
include("TrivialCats.jl")
include("DiscreteCats.jl")

@reexport using .TypeCats
@reexport using .OpCats
@reexport using .TrivialCats
@reexport using .DiscreteCats

end # module
