using BenchmarkTools

const SUITE = BenchmarkGroup()

include("Graphs.jl")

SUITE["Graphs"] = BenchmarkGraphs.SUITE
