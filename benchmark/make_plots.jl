include("benchmarks.jl")

include("plots.jl")

results = run(SUITE)
data = graphbench_data(results)
plot_all_subcats(data)
