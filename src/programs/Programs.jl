""" Generate and parse computer programs representing morphisms.
"""
module Programs

using Reexport

include("GenerateJuliaPrograms.jl")
include("ParseJuliaPrograms.jl")
include("ParseRelations.jl")

@reexport using .GenerateJuliaPrograms
@reexport using .ParseJuliaPrograms
@reexport using .ParseRelations

end
