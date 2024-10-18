""" Contains ADT reprsentations of core CatLab structures.
"""
module ADTs 

using Reexport

include("RelationTerm.jl")

@reexport using .RelationTerm

end