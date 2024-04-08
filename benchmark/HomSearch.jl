# Benchmark various hom search algorithms against each other.
# In the future, benchmark against external solvers, too.

using BenchmarkTools
const SUITE = BenchmarkGroup()

using Random
using Catlab

Random.seed!(1)

bench = SUITE["HomSearch"] = BenchmarkGroup()
btsbench = bench["Backtracking"] = BenchmarkGroup()
vmnbench = bench["VM_neighbor"] = BenchmarkGroup()
vmcbench = bench["VM_connected"] = BenchmarkGroup()

# DDS
#####

@present SchDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end

@acset_type DDS(SchDDS, index=[:Φ])

DDS(i::Int) = @acset DDS begin X=i; Φ=[rand(1:i) for _ in 1:i] end # random DDS

small_dds = [DDS(5) for _ in 1:2]
big_dds = [DDS(200) for _ in 1:2]

prog1 = compile_hom_search.(small_dds, strat=:neighbor);
prog2 = compile_hom_search.(small_dds, strat=:connected);

for (i, x) in enumerate(small_dds), (j, y) in enumerate(big_dds)
  btsbench["DDS-$i-$j"] = @benchmarkable homomorphisms($x, $y)
  vmnbench["DDS-$i-$j"] = @benchmarkable homomorphisms($x, $y; alg=VMSearch(), prog=$(prog1[i]))
  vmcbench["DDS-$i-$j"] = @benchmarkable homomorphisms($x, $y; alg=VMSearch(), prog=$(prog2[i]))
end

# Graph
#######

c3 = cycle_graph(Graph, 3)

prog1 = compile_hom_search(c3, strat=:neighbor);
prog2 = compile_hom_search(c3, strat=:connected);

for (i, G) in [(i, erdos_renyi(Graph, 150, 0.05)) for i in 1:5]
  btsbench["graph-$i"] = @benchmarkable homomorphisms($c3, $G)
  vmnbench["graph-$i"] = @benchmarkable homomorphisms($c3, $G; alg=VMSearch(), prog=$prog1)
  vmcbench["graph-$i"] = @benchmarkable homomorphisms($c3, $G; alg=VMSearch(), prog=$prog2)
end

