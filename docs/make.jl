using Documenter
using Literate

const literate_dir = joinpath(@__DIR__, "literate")
const generated_dir = joinpath(@__DIR__, "src", "generated")

@info "Loading Catlab.jl"
using Catlab

@info "Building Literate.jl docs"
for (root, dirs, files) in walkdir(literate_dir)
  out_dir = joinpath(generated_dir, relpath(root, literate_dir))
  for file in files
    if last(splitext(file)) == ".jl"
      Literate.markdown(joinpath(root, file), out_dir;
        documenter=true, credit=false)
      Literate.notebook(joinpath(root, file), out_dir;
        execute=true, documenter=true, credit=false)
    end
  end
end

@info "Building Documenter.jl docs"
makedocs(
  modules     = [Catlab],
  format      = Documenter.HTML(),
  sitename    = "Catlab.jl",
  doctest     = false,
  pages       = Any[
    "Catlab.jl" => "index.md",
    "Tutorials" => Any[
      "generated/wiring_diagrams/wiring_diagram_basics.md",
      "generated/wiring_diagrams/diagrams_and_expressions.md",
      "generated/graphics/graphviz_wiring_diagrams.md",
      "generated/graphics/tikz_wiring_diagrams.md",
      "generated/programs/algebraic_nets.md",
    ],
    "APIs"      => Any[
      "apis/index.md",
      "apis/catlab.md",
      "apis/doctrines.md",
      "apis/wiring_diagrams.md",
      "apis/graphics.md",
      "apis/programs.md",
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
