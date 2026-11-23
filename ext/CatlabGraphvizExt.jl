module CatlabGraphvizExt

using Graphviz_jll

import Catlab.Graphics.Graphviz: gv_backend

# Call the JLL executable with no arguments to get a `Cmd` that carries the
# environment (library paths) the binary needs. The older `prog(identity)` form
# returns only the bare path, so the binary cannot find its shared libraries.
gv_backend(::Type{Val{:graphviz_jll}}, prog) = getfield(Graphviz_jll, Symbol(prog))()

function __init__()
  # Graphviz_jll 15+ ships its plugin configuration file (`config8`), but
  # Graphviz_jll 2.x does not, so generate one if it is missing.
  gvdir = joinpath(Graphviz_jll.artifact_dir, "lib", "graphviz")
  if isdir(gvdir) && !any(startswith("config"), readdir(gvdir))
    run(`$(Graphviz_jll.dot()) -c`)
  end
end

end
