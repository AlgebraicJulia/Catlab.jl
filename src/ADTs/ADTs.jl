""" Contains ADT reprsentations of core CatLab structures.
"""
module ADTs 

using Reexport

include("RelationTerm.jl")
include("ADTsBase.jl")

@reexport using .RelationTerm
@reexport using .ADTsBase

end