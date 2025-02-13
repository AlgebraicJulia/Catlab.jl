using BenchmarkTools
const SUITE = BenchmarkGroup()

using Random
using Catlab.CategoricalAlgebra, Catlab.BasicSets
using Catlab.CategoricalAlgebra.SetCats.FinSetCat.FinSetCatLimits: 
  nested_loop_limit, sort_merge_limit, hash_join

bench = SUITE["Limits"] = BenchmarkGroup()

function benchmark_pullback(suite::BenchmarkGroup, name, cospan)
  @benchmarkable suite["$name:NestedLoopJoin"] = nested_loop_limit($cospan)
  @benchmarkable suite["$name:SortMergeJoin"] = sort_merge_limit($cospan)
  @benchmarkable suite["$name:HashJoin"] = hash_join($cospan)
end

sizes = (100, 150)
f, g = (FinFunction(ones(Int, size), 1) for size in sizes)
benchmark_pullback(bench, "pullback_terminal", Cospan(f, g))

f = FinFunction(identity, FinSet(10000), FinSet(10000))
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
