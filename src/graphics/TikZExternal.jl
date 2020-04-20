# External packages.
import .TikzPictures: TikzPicture

import .TikZ

""" Convert TikZ document to `TikzPicture` object (from `TikzPictures.jl`).
"""
function TikzPicture(doc::TikZ.Document; preamble::String="")::TikzPicture
  data = join(sprint(TikZ.pprint, stmt) for stmt in doc.picture.stmts)
  options = join((sprint(TikZ.pprint, prop) for prop in doc.picture.props), ",")
  preamble = join([ preamble;
    [ "\\usepackage{$package}" for package in doc.packages ];
    [ "\\usetikzlibrary{$library}" for library in doc.libraries ];
  ], "\n")
  TikzPicture(data; options=options, preamble=preamble)
end

function Base.show(io::IO, ::MIME"image/svg+xml", doc::TikZ.Document)
  show(io, MIME"image/svg+xml"(), TikzPicture(doc))
end
