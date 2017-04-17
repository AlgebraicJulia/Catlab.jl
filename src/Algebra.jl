""" A module for traditional computer algebra from a categorical point of view.
"""
module Algebra

include("algebra/Network.jl")

using Reexport
@reexport using .Network

end
