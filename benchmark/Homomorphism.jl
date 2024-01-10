include("./Support/graph_bank.jl")
using BenchmarkTools

numSamples = 1000
BenchmarkTools.DEFAULT_PARAMETERS.samples = numSamples
const SUITE = BenchmarkGroup()

# Begin Graph Homs
##################
# Grid Graphs (Using Reflexive Graphs)
#-------------------------------------
n = 10
SUITE["grids"] = BenchmarkGroup()
SUITE["grids"]["Reflexive gridToPath"] = @benchmarkable gridToPath($n)
SUITE["grids"]["Reflexive pathToGrid"] = @benchmarkable pathToGrid($n)

function gridToPath(n)
    for i in 1:n
        component = path_graph(ReflexiveGraph, i) # generate path graph of size i
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom = add_loops(component) # add loops to the codomain
        homomorphism(checkerboard, codom) # generate homomorphism ***GRID -> PATH***
    end
end

function pathToGrid(n)
    for i in 1:n
        component = path_graph(ReflexiveGraph, i) # generate path graph of size i
        checkerboard = box_product(component, component) # generate grid graph based on the component graph
        codom = add_loops(checkerboard) # add loops to the codomain
        homomorphism(component, codom) # generate homomorphism ***PATH -> GRID***
    end
end

# Sparse Acyclic Graphs
#----------------------
SUITE["gtoh"] = BenchmarkGroup()
SUITE["gtoh"]["Sparse Acyclic gLarger"] = @benchmarkable gLarger()
SUITE["gtoh"]["Sparse Acyclic hLarger"] = @benchmarkable hLarger()
SUITE["gtoh"]["Sparse Acyclic Analogous"] = @benchmarkable analogous()

# G larger than H for G->H
function gLarger()
    homomorphism(a_sparse_six2, loop_sparse_four)
    homomorphism(a_sparse_eight, loop_sparse_seven)
    homomorphism(a_sparse_eight2, loop_sparse_six)
    homomorphism(a_sparse_five, loop_sparse_three)
    homomorphism(large1, loop_sparse_five)
    homomorphism(large1, loop_sparse_three)
    homomorphism(large2, loop_sparse_three)
    homomorphism(large2, loop_sparse_six)
    homomorphism(large3, loop_sparse_seven)
    homomorphism(large3, loop_sparse_eight)
    homomorphism(large4, loop_sparse_eight)
    homomorphism(large4, loop_large1)
    homomorphism(large5, loop_large2)
    homomorphism(large5, loop_large3)
    homomorphism(large6, loop_large3)
    homomorphism(large7, loop_large4)
end

# H larger than G for G->H
function hLarger()
    homomorphism(a_sparse_four, loop_sparse_six2)
    homomorphism(a_sparse_seven, loop_sparse_eight)
    homomorphism(a_sparse_six, loop_sparse_eight2)
    homomorphism(a_sparse_three, loop_sparse_five)
    homomorphism(a_sparse_five, loop_large1)
    homomorphism(a_sparse_three, loop_large1)
    homomorphism(a_sparse_three, loop_large2)
    homomorphism(a_sparse_six, loop_large2)
    homomorphism(a_sparse_seven, loop_large3)
    homomorphism(a_sparse_eight, loop_large3)
    homomorphism(a_sparse_eight, loop_large4)
    homomorphism(large1, loop_large4)
    homomorphism(large2, loop_large5)
    homomorphism(large3, loop_large5)
    homomorphism(large3, loop_large6)
    homomorphism(large4, loop_large7)
end

# G similar in size to H for G->H
function analogous()
    homomorphism(a_sparse_five, loop_sparse_five)
    homomorphism(a_sparse_eight, loop_sparse_eight)
    homomorphism(a_sparse_seven, loop_sparse_eight2)
    homomorphism(a_sparse_eight, loop_sparse_seven)
    homomorphism(a_sparse_three, loop_sparse_four)
    homomorphism(a_sparse_six, loop_sparse_five)
    homomorphism(a_sparse_four, loop_sparse_five)
    homomorphism(a_sparse_five, loop_sparse_four)
    homomorphism(a_sparse_four, loop_sparse_three)
    homomorphism(a_sparse_seven, loop_sparse_eight)
    homomorphism(a_sparse_six, loop_sparse_six2)
    homomorphism(a_sparse_six2, loop_sparse_five)
    homomorphism(a_sparse_five, loop_sparse_six2)
end

# Complete Graphs
#----------------
SUITE["complete"] = BenchmarkGroup()
SUITE["complete"]["Complete gLarger"] = @benchmarkable c_gLarger()
SUITE["complete"]["Complete hLarger"] = @benchmarkable c_hLarger()
SUITE["complete"]["Complete identical"] = @benchmarkable c_identical()

length(complete_list)

function c_gLarger()
    len = length(complete_list)
    # avoid references - copying could work
    j = 1
    for i in len:-1:convert(Int64, len / 2)
        homomorphism(complete_list[i], loop_complete_list[j])
        j += 1
    end
end

function c_hLarger()
    len = length(complete_list)
    # avoid references - copying could work
    j = length(complete_list)
    for i in 1:convert(Int64, len / 2)
        homomorphism(complete_list[i], loop_complete_list[j])
        j -= 1
    end
end

function c_identical()
    for i in 1:length(complete_list)
        homomorphism(complete_list[i], loop_complete_list[i])
    end
end

# Simplicial Sets
#################
SUITE["simplicial"] = BenchmarkGroup()
SUITE["simplicial"]["quad pattern"] = @benchmarkable quad_pattern()
SUITE["simplicial"]["1d pattern"] = @benchmarkable od_pattern()

function quad_pattern()
    for i in quad_list
        homomorphism(quad, i)
    end
end

function od_pattern()
    for i in ss_list
        for j in od_list
            homomorphism(i, j)
            homomorphism(j, i)
        end
    end
end

# Tune and run
tune!(SUITE);
results = run(SUITE, verbose=true, seconds=5)