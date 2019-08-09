module TestYFilesWiringDiagrams

using Test
using LightXML
using Catlab.WiringDiagrams

const data_dir = joinpath(@__DIR__, "data")

diagram = read_yfiles_diagram(joinpath(data_dir, "yed.graphml"))

end
