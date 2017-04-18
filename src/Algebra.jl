""" A module for traditional computer algebra from a categorical point of view.
"""
module Algebra

include("algebra/Network.jl")
include("algebra/Tree.jl")

using Reexport
@reexport using .Network
@reexport using .Tree

end
