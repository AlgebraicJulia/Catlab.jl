using BenchmarkTools

const SUITE = BenchmarkGroup()

module BenchmarkFinSets
  include("FinSets.jl")
end

module BenchmarkGraphs
  include("Graphs.jl")
end

SUITE["FinSets"] = BenchmarkFinSets.SUITE
SUITE["Graphs"] = BenchmarkGraphs.SUITE
