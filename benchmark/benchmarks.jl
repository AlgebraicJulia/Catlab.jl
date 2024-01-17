using BenchmarkTools

const SUITE = BenchmarkGroup()

module BenchmarkHomSearch
  include("HomSearch.jl")
end

module BenchmarkFinSets
  include("FinSets.jl")
end

module BenchmarkGraphs
  include("Graphs.jl")
end

SUITE["HomSearch"] = BenchmarkHomSearch.SUITE
SUITE["FinSets"] = BenchmarkFinSets.SUITE
SUITE["Graphs"] = BenchmarkGraphs.SUITE
