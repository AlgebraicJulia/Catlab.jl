module Interactive
export TikzPicture

import Base: show
import TikzPictures: TikzPicture
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

function show(f::IO, ::MIME"image/svg+xml", pic::TikZ.Picture)
  show(f, MIME"image/svg+xml"(), TikzPicture(pic))
end

end
