""" Generate and parse computer programs representing morphisms.
"""
module Programs

using Reexport

include("GenerateJuliaPrograms.jl")
include("ParseJuliaPrograms.jl")

@reexport using .GenerateJuliaPrograms
@reexport using .ParseJuliaPrograms

end
