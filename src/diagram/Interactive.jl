module Interactive
export TikzPicture

import Base: show
import TikzPictures: TikzPicture

using ...Syntax
import ..TikZ

""" Convert our TikZ picture type to `TikzPicture`'s picture type. 
"""
function TikzPicture(pic::TikZ.Picture; usePDF2SVG=true)::TikzPicture
  data = join(sprint(TikZ.pprint, stmt) for stmt in pic.stmts)
  options = join((sprint(TikZ.pprint, prop) for prop in pic.props), ",")
  preamble = join([
    # FIXME: Dependencies are hard-coded!
    "\\usetikzlibrary{calc}",
    "\\usetikzlibrary{decorations.markings}",
    "\\usetikzlibrary{positioning}",
  ], "\n")
  TikzPicture(data; options=options, preamble=preamble, usePDF2SVG=usePDF2SVG)
end

function show(io::IO, ::MIME"image/svg+xml", pic::TikZ.Picture)
  show(io, MIME"image/svg+xml"(), TikzPicture(pic))
end

function show(io::IO, ::MIME"text/latex", expr::BaseExpr)
  print(io, "\$")
  show_latex(io, expr)
  print(io, "\$")
end

end
