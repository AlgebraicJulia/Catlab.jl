"""
Functionality related to search problems involving ACSets, e.g.:

- enumerating Hom(X,Y) where X,Y are ACSets
- enumerating subobjects of an ACSet, X
- enumerating partial overlaps between ACSets
"""
module HomSearch 

using Reexport 

include("HomSearch.jl")

include("VMHomSearch.jl")
@reexport using .VMHomSearch

include("MCO.jl")
@reexport using .MCO

end # module
