module TestYFilesWiringDiagrams

using Test
using Catlab.WiringDiagrams

read_yfiles(name::String; kw...) =
  read_yfiles_diagram(joinpath(@__DIR__, "data", name); kw...)

diagram_vertical = read_yfiles("yed_vertical.graphml", direction=:vertical)
println(diagram_vertical)

diagram_horizontal = read_yfiles("yed_horizontal.graphml", direction=:horizontal)
println(diagram_horizontal)

end
