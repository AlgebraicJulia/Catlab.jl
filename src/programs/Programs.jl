""" Generate and parse computer programs representing morphisms.
"""
module Programs

using Reexport

include("GenerateJuliaPrograms.jl")
include("ParseJuliaPrograms.jl")
include("RelationalPrograms.jl")

@reexport using .GenerateJuliaPrograms
@reexport using .ParseJuliaPrograms
@reexport using .RelationalPrograms

end
