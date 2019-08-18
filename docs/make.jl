using Documenter

@info "Loading module"
using Catlab

@info "Making docs"
makedocs(
  modules     = [Catlab],
  format      = Documenter.HTML(),
  sitename    = "Catlab",
  doctest     = false,
  pages       = Any[
    "Catlab.jl" => "index.md",
    "APIs"      => Any[
      "apis/index.md",
      "apis/catlab.md",
      "apis/algebra.md",
      "apis/doctrines.md",
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
