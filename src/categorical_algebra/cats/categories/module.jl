module Categories

using Reexport

include("Categories.jl")

include("TypeCats.jl")
@reexport using .TypeCats

include("OpCats.jl")
@reexport using .OpCats

include("TrivialCats.jl")
@reexport using .TrivialCats

include("DiscreteCats.jl")
@reexport using .DiscreteCats

include("CoproductCats.jl")
@reexport using .CoproductCats


end # module
