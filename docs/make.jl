using Documenter
using Literate

const literate_dir = joinpath(@__DIR__, "literate")
const generated_dir = joinpath(@__DIR__, "src", "generated")

@info "Loading Catlab.jl"
using Catlab,
  # Must explicitly load all submodules for which docs are needed.
  Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs,
  Catlab.WiringDiagrams, Catlab.Graphics, Catlab.Programs

const no_literate = "--no-literate" in ARGS
if !no_literate
  @info "Building Literate.jl docs"

  # XXX: Work around old LaTeX distribution in GitHub CI.
  if haskey(ENV, "GITHUB_ACTIONS")
    import TikzPictures
    TikzPictures.standaloneWorkaround(true)
  end

  # Set Literate.jl config if not being compiled on recognized service.
  config = Dict{String,String}()
  if !(haskey(ENV, "GITHUB_ACTIONS") || haskey(ENV, "GITLAB_CI"))
    config["nbviewer_root_url"] = "https://nbviewer.jupyter.org/github/AlgebraicJulia/Catlab.jl/blob/gh-pages/dev"
    config["repo_root_url"] = "https://github.com/AlgebraicJulia/Catlab.jl/blob/master/docs"
  end

  for (root, dirs, files) in walkdir(literate_dir)
    out_dir = joinpath(generated_dir, relpath(root, literate_dir))
    for file in files
      if last(splitext(file)) == ".jl"
        Literate.markdown(joinpath(root, file), out_dir;
                          config=config, documenter=true, credit=false)
        Literate.notebook(joinpath(root, file), out_dir;
                          execute=true, documenter=true, credit=false)
      end
    end
  end
end

@info "Building Documenter.jl docs"
makedocs(
  modules     = [Catlab],
  format      = Documenter.HTML(
                                assets = ["assets/analytics.js"],
                               ),
  sitename    = "Catlab.jl",
  doctest     = false,
  checkdocs   = :none,
  pages       = Any[
    "Catlab.jl" => "index.md",
    "Vignettes" => no_literate ? [] : Any[
      "Seven Sketches in Compositionality" => Any[
        "generated/sketches/partitions.md",
        "generated/sketches/preorders.md",
        "generated/sketches/meets.md",
        "generated/sketches/smc.md",
        "generated/sketches/cat_elements.md"
        ],
      "Graphs" => Any[
        "generated/graphs/graphs.md",
        "generated/graphs/graphs_label.md",
        "generated/graphs/subgraphs.md",
      ],
      "Categorical Algebra" => Any[
        "generated/categorical_algebra/diagrams.md",
        "generated/categorical_algebra/acset_serialization.md",
      ],
      "Wiring Diagrams" => Any[
        "generated/wiring_diagrams/wiring_diagram_basics.md",
        "generated/wiring_diagrams/diagrams_and_expressions.md",
        "generated/wiring_diagrams/wd_cset.md",
      ],
      "Graphics" => Any[
        "generated/graphics/graphviz_graphs.md",
        "generated/graphics/graphviz_wiring_diagrams.md",
        "generated/graphics/composejl_wiring_diagrams.md",
        "generated/graphics/tikz_wiring_diagrams.md",
        "generated/graphics/layouts_vs_drawings.md",
      ],
    ],
    "Modules" => Any[
      "apis/core.md",
      "apis/theories.md",
      "apis/categorical_algebra.md",
      "apis/graphs.md",
      "apis/wiring_diagrams.md",
      "apis/graphics.md",
      "apis/programs.md",
    ],
    "Developer Docs" => Any[
      "devdocs/style.md",
    ],
  ]
)

@info "Deploying docs"
deploydocs(
  target = "build",
  repo   = "github.com/AlgebraicJulia/Catlab.jl.git",
  branch = "gh-pages"
)
