""" 2-category of finitely presented categories.

This module is for the 2-category **Cat** what the module [`FinSets`](@ref) is
for the category **Set**: a finitary, combinatorial setting where explicit
calculations can be carried out. We emphasize that the prefix `Fin` means
"finitely presented," not "finite," as finite categories are too restrictive a
notion for many purposes. For example, the free category on a graph is finite if
and only if the graph is DAG, which is a fairly special condition. This usage of
`Fin` is also consistent with `FinSet` because for sets, being finite and being
finitely presented are equivalent.
"""
module FinCats
using Reexport

include("FinCats.jl")
include("PathCats.jl")
include("PreorderCats.jl")
include("OpFinCat.jl")
include("FinCatGraphs.jl")
include("FinCatPres.jl")
include("FinCatsAsCats.jl")

@reexport using .PathCats
@reexport using .PreorderCats
@reexport using .OpFinCat
@reexport using .FinCatGraphs
@reexport using .FinCatPres
@reexport using .FinCatsAsCats

end # module
