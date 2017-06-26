""" A module for traditional computer algebra from a categorical point of view.
"""
module Algebra

using Reexport

include("Network.jl")
include("Tree.jl")

@reexport using .Network
@reexport using .Tree

end
