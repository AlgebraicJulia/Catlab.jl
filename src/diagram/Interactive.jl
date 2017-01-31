module Interactive
export TikzPicture

import TikzPictures: TikzPicture
import ..TikZ

""" Convert our TikZ picture type to `TikzPicture`'s picture type. 
"""
function TikzPicture(pic::TikZ.Picture; usePDF2SVG=true)::TikzPicture
  data = join(TikZ.spprint(stmt) for stmt in pic.stmts)
  options = join((TikZ.spprint(prop) for prop in pic.props), ",")
  preamble = join([
    # FIXME: Dependencies are hard-coded!
    "\\usetikzlibrary{calc}",
    "\\usetikzlibrary{decorations.markings}",
    "\\usetikzlibrary{graphdrawing}",
    "\\usetikzlibrary{graphs}",
    "\\usegdlibrary{layered}",
  ], "\n")
  TikzPicture(data; options=options, preamble=preamble, usePDF2SVG=usePDF2SVG)
end

end
