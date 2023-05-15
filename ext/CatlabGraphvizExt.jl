module CatlabGraphvizExt

using Graphviz_jll

import Catlab.Graphics.Graphviz: gv_backend

gv_backend(::Type{Val{:graphviz_jll}}, prog) = getfield(Graphviz_jll, Symbol(prog))(identity)

let cfg = joinpath(Graphviz_jll.artifact_dir, "lib", "graphviz", "config6")
  if !isfile(cfg)
    Graphviz_jll.dot(path -> run(`$path -c`))
  end
end

end
