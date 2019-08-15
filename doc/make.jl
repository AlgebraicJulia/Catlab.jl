using Documenter

@info "Loading module"
using Catlab
@info "Making docs"
makedocs(
modules     = [Catlab],
root        = "doc",
format      = Documenter.HTML(),
sitename    = "Catlab",
doctest     = false,
pages       = Any[
    "Catlab.jl" => "index.md",
    "APIs"      => Any[
                       "apis/index.md",
                       "apis/catlab.md",
                       "apis/algebra.md",
                       "apis/doctorines.md",
                       "apis/graphics.md",
                       "apis/wiringdiagrams.md",
                      ]
]
)

#deploydocs(
#target      = "build",
#deps        = nothing,
#make        = nothing,
#repo        = "https://github.com/epatters/Catlab.jl",
#)
