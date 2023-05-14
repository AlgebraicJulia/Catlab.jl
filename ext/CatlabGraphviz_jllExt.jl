module CatlabGraphviz_jllExt

using Graphviz_jll

using Catlab.Graphics.Graphviz

Graphviz.USE_GV_JLL[] = true
let cfg = joinpath(Graphviz_jll.artifact_dir, "lib", "graphviz", "config6")
  if !isfile(cfg)
    Graphviz_jll.dot(path -> run(`$path -c`))
  end
end

end
