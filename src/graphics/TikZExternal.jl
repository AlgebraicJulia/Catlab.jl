import .TikzPictures: TikzPicture

# External library import.
import .TikZ

""" Convert our TikZ picture type to `TikzPicture`'s picture type. 
"""
function TikzPicture(pic::TikZ.Picture; preamble::String="")::TikzPicture
  data = join(sprint(TikZ.pprint, stmt) for stmt in pic.stmts)
  options = join((sprint(TikZ.pprint, prop) for prop in pic.props), ",")
  preamble = join([
    preamble,
    "\\usepackage{amssymb}",
    # FIXME: These TikZ library dependencies should be stored in TikZ.Picture.
    "\\usetikzlibrary{arrows.meta}",
    "\\usetikzlibrary{calc}",
    "\\usetikzlibrary{decorations.markings}",
    "\\usetikzlibrary{positioning}",
    "\\usetikzlibrary{shapes.geometric}",
  ], "\n")
  TikzPicture(data; options=options, preamble=preamble)
end

function Base.show(io::IO, ::MIME"image/svg+xml", pic::TikZ.Picture)
  show(io, MIME"image/svg+xml"(), TikzPicture(pic))
end
