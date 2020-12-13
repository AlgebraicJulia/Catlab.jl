using BenchmarkTools
const SUITE = BenchmarkGroup()

using Random
using Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets

bench = SUITE["Limits"] = BenchmarkGroup()

function benchmark_pullback(suite::BenchmarkGroup, name, cospan)
  for alg in (NestedLoopJoin(), SortMergeJoin(), HashJoin())
    suite["$name:$(nameof(typeof(alg)))"] =
      @benchmarkable limit($cospan, alg=$alg)
  end
end

m, n = 100, 150
f, g = FinFunction(ones(Int, m), 1), FinFunction(ones(Int, n), 1)
benchmark_pullback(bench, "pullback_terminal", Cospan(f, g))

f = FinFunction(identity, FinSet(10000))
benchmark_pullback(bench, "pullback_identity", Cospan(f, f))

n = 10000
Random.seed!(1)
f, g = FinFunction(randperm(n), n), FinFunction(randperm(n), n)
benchmark_pullback(bench, "pullback_randperm", Cospan(f, g))

k = 1000
m, n = 9000, 11000
Random.seed!(1)
f, g = FinFunction(rand(1:k, m), k), FinFunction(rand(1:k, n), k)
benchmark_pullback(bench, "pullback_randsparse", Cospan(f, g))
