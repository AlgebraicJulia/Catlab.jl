using BenchmarkTools
const SUITE = BenchmarkGroup()

using Random
using Catlab.CategoricalAlgebra

bench = SUITE["Limits"] = BenchmarkGroup()

function benchmark_pullback(suite::BenchmarkGroup, name, cospan)
  for alg in (NestedLoopJoin(), SortMergeJoin(), HashJoin())
    suite["$name:$(nameof(typeof(alg)))"] =
      @benchmarkable limit($cospan, alg=$alg)
  end
end

sizes = (100, 150)
f, g = (FinFunction(ones(Int, size), 1) for size in sizes)
benchmark_pullback(bench, "pullback_terminal", Cospan(f, g))

f = FinFunction(identity, FinSet(10000))
benchmark_pullback(bench, "pullback_identity", Cospan(f, f))

n = 10000
Random.seed!(1)
f, g = FinFunction(randperm(n), n), FinFunction(randperm(n), n)
benchmark_pullback(bench, "pullback_randperm", Cospan(f, g))

k = 1000
sizes = (9000, 11000)
Random.seed!(1)
f, g = (FinFunction(rand(1:k, size), k) for size in sizes)
benchmark_pullback(bench, "pullback_randsparse", Cospan(f, g))

k = 50
sizes = (400, 500, 600)
Random.seed!(1)
f, g, h = (FinFunction(rand(1:k, size), k) for size in sizes)
benchmark_pullback(bench, "ternary_pullback_randsparse",
                   SMulticospan{3}(f, g, h))
