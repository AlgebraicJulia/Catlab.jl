using Documenter
using Literate

const literate_dir = Dict(
  :jl => joinpath(@__DIR__, "literate"),
  :md => joinpath(@__DIR__, "src", "tutorials"),
  :nb => joinpath(@__DIR__, "notebooks"),
)

@info "Loading module"
using Catlab

@info "Building tutorial docs"
for (root, dirs, files) in walkdir(literate_dir[:jl])
  relroot = relpath(root, literate_dir[:jl])
  md_dir = joinpath(literate_dir[:md], relroot)
  nb_dir = joinpath(literate_dir[:nb], relroot)
  for file in files
    if last(splitext(file)) == ".jl"
      Literate.markdown(joinpath(root, file), md_dir;
        documenter=true, credit=false)
      Literate.notebook(joinpath(root, file), nb_dir;
        execute=true, documenter=true, credit=false)
    end
  end
end

@info "Building API docs"
makedocs(
  modules     = [Catlab],
  format      = Documenter.HTML(),
  sitename    = "Catlab.jl",
  doctest     = false,
  pages       = Any[
    "Catlab.jl" => "index.md",
    "Tutorials" => Any[
      "tutorials/wiring_diagrams/wiring_diagram_basics.md",
      "tutorials/wiring_diagrams/diagrams_and_expressions.md",
      "tutorials/graphics/graphviz_wiring_diagrams.md",
      "tutorials/graphics/tikz_wiring_diagrams.md",
      "tutorials/algebra/algebraic_nets.md",
    ],
    "APIs"      => Any[
      "apis/index.md",
      "apis/catlab.md",
      "apis/doctrines.md",
      "apis/wiringdiagrams.md",
      "apis/graphics.md",
      "apis/algebra.md",
    ]
  ]
)

@info "Deploying docs"
deploydocs(
  target = "build",
  repo   = "github.com/epatters/Catlab.jl.git",
  branch = "gh-pages",
  deps   = nothing,
  make   = nothing
)
