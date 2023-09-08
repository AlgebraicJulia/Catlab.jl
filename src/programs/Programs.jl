""" Generate and parse Julia programs based on diagrams.
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
