using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
using Plots

# add_loops
# returns a graph with loops on the user-provided vertices
# valid g input consists of Catlab ACSet graphs
# valid vs input consists of lists or integer UnitRanges
add_loops!(g, vs) = add_parts!(g, :E, length(vs), src=vs, tgt=vs)
add_loops(g, vs) = begin
    h = copy(g)
    add_loops!(h, vs)
    return h
end

# general version to add loops to all vertices of a graph
add_loops(g) = begin
    h = copy(g)
    add_loops!(h, parts(h, :V))
    return h
end

# Auto Calculation and Plotting
# Uses the product of the two provided lists to find approximate homomorphism performance.
# Save parameter is a boolean value indicating the intent to save the resulting plots. This defaults to false to avoid creating unwanted files.
# Sample size refers to the number of BenchmarkTools samples are to be run to calculate a median time. This defaults to 100 to avoid long runtimes.
function autoPlot(fromList, toList, save=false, sampleSize=100)
    length(fromList) == length(toList) || error("Arguments fromList and toList should be of equal lengths. fromList had a length of $(length(fromList)) and toList had a length of $(length(toList)).")
    BenchmarkTools.DEFAULT_PARAMETERS.samples = sampleSize
    operationList = Base.Iterators.product(fromList, toList)
    println("Autoplotting Homs...           Note: The runtime will depend on the complexity and size of your sets.\nTotal pairs: $(length(operationList))")
    plotGenerate(operationList, save)
    println("Complete!")
end

# Uses the zip of the two provided lists to find approximate homomorphism performance.
# Save parameter is a boolean value indicating the intent to save the resulting plots. This defaults to false to avoid creating unwanted files.
# Sample size refers to the number of BenchmarkTools samples are to be run to calculate a median time. This defaults to 100 to avoid long runtimes.
function quickPlot(fromList, toList, save=false, sampleSize=100)
    length(fromList) == length(toList) || error("Arguments fromList and toList should be of equal lengths. fromList had a length of $(length(fromList)) and toList had a length of $(length(toList)).")
    BenchmarkTools.DEFAULT_PARAMETERS.samples = sampleSize
    operationList = Base.Iterators.zip(fromList, toList)
    println("Autoplotting Homs...           Note: The runtime will depend on the complexity and size of your sets.\nTotal pairs: $(length(operationList))")
    plotGenerate(operationList, save)
    println("Complete!")
end

# Helper function for automatic plotting. - Reduces clutter.
function plotGenerate(list, save)
    x1 = Int64[]
    x2 = Int64[]
    x3 = Int64[]
    x4 = Int64[]
    y1 = Float64[]
    for i in list
        tempY = time(median(@benchmark homomorphism($i[1], $i[2]))) / 1000000
        append!(y1, tempY)
        append!(x1, length(vertices(i[1])))
        append!(x2, length(edges(i[1])))
        append!(x3, length(vertices(i[2])))
        append!(x4, length(edges(i[2])))
    end
    if save
        scatter([x1], [y1], title="Autoplotted Graph Vertices", xlabel="Number of \"From\" Vertices", ylabel="Single Hom Calculation Time (sec)", legend=false)
        savefig("quickFromVertex.png")
        scatter([x2], [y1], title="Autoplotted Graph Edges", xlabel="Number of \"From\" Edges", ylabel="Single Hom Calculation Time (sec)", legend=false)
        savefig("quickFromEdge.png")
        scatter([x3], [y1], title="Autoplotted Graph Vertices", xlabel="Number of \"To\" Vertices", ylabel="Single Hom Calculation Time (sec)", legend=false)
        savefig("quickToVertex.png")
        scatter([x4], [y1], title="Autoplotted Graph Edges", xlabel="Number of \"To\" Edges", ylabel="Single Hom Calculation Time (sec)", legend=false)
        savefig("quickToEdge.png")
    else
        display(scatter([x1], [y1], title="Autoplotted Graph Vertices", xlabel="Number of \"From\" Vertices", ylabel="Single Hom Calculation Time (sec)", legend=false))
        display(scatter([x2], [y1], title="Autoplotted Graph Edges", xlabel="Number of \"From\" Edges", ylabel="Single Hom Calculation Time (sec)", legend=false))
        display(scatter([x3], [y1], title="Autoplotted Graph Vertices", xlabel="Number of \"To\" Vertices", ylabel="Single Hom Calculation Time (sec)", legend=false))
        display(scatter([x4], [y1], title="Autoplotted Graph Edges", xlabel="Number of \"To\" Edges", ylabel="Single Hom Calculation Time (sec)", legend=false))
    end
end

# Generates and appends new graphs to the given list
function autoGen(graphs, vertexLimit, edgeLimit)
    vertexLimit >= 1 && edgeLimit >= 1 || error("Arguments vertexLimit and edgeLimit should be at least 1. Received vertexLimit $vertexLimit and edgeLimit $edgeLimit.")
    #keep original list length since it will change
    original = length(graphs)
    for i in 1:original
        base = graphs[i]
        larger = apex(product(base, add_loops(base)))
        while length(vertices(larger)) < vertexLimit && length(edges(larger)) < edgeLimit
            append!(graphs, [larger])
            larger = apex(product(base, add_loops(larger)))
        end
    end
end

# Generates and appends new graphs to the given lists - autoGen, but *plural*
# It keeps the list sizes consistent and aligned.
function autoGens(fromGraphs, toGraphs, vertexLimit, edgeLimit)
    vertexLimit >= 1 && edgeLimit >= 1 || error("Arguments vertexLimit and edgeLimit should be at least 1. Received vertexLimit $vertexLimit and edgeLimit $edgeLimit.")
    length(fromGraphs) == length(toGraphs) || error("Arguments fromGraphs and toGraphs should be of equal lengths. fromGraphs had a length of $(length(fromGraphs)) and toGraphs had a length of $(length(toGraphs)).")
    #keep original list length since it will change
    original = length(toGraphs)
    for i in 1:original
        println("Calculating $i of $original")
        fromBase = fromGraphs[i]
        fromLarger = apex(product(fromBase, add_loops(fromBase)))
        toBase = toGraphs[i]
        toLarger = apex(product(toBase, add_loops(toBase)))
        while length(vertices(fromLarger)) < vertexLimit && length(edges(fromLarger)) < edgeLimit && length(vertices(toLarger)) < vertexLimit && length(edges(toLarger)) < edgeLimit
            append!(fromGraphs, [fromLarger])
            append!(toGraphs, [toLarger])
            fromLarger = apex(product(fromBase, add_loops(fromLarger)))
            toLarger = apex(product(toBase, add_loops(toLarger)))
        end
    end
end

function autoShuffle(fromGraphs, toGraphs, vertexLimit, edgeLimit)
    vertexLimit >= 1 && edgeLimit >= 1 || error("Arguments vertexLimit and edgeLimit should be at least 1. Received vertexLimit $vertexLimit and edgeLimit $edgeLimit.")
    length(fromGraphs) == length(toGraphs) || error("Arguments fromGraphs and toGraphs should be of equal lengths. fromGraphs had a length of $(length(fromGraphs)) and toGraphs had a length of $(length(toGraphs)).")
    println("Shuffling...")
    #keep original list length since it will change
    original = length(toGraphs)
    total = length(toGraphs) * (length(toGraphs) - 1)
    count = 1
    for i in 1:original
        for j in 1:original
            if j == i
                continue
            end
            println("Calculating $count of $total")
            count = count + 1
            prod = apex(product(fromGraphs[i], add_loops(fromGraphs[j])))
            prod2 = apex(product(toGraphs[i], add_loops(toGraphs[j])))
            if length(vertices(prod)) < vertexLimit && length(edges(prod)) < edgeLimit && length(vertices(prod2)) < vertexLimit && length(edges(prod2)) < edgeLimit
                append!(fromGraphs, [prod])
                append!(toGraphs, [prod2])
            end
        end
    end
end

function autoShuffleThorough(fromGraphs, toGraphs, vertexLimit, edgeLimit)
    vertexLimit >= 1 && edgeLimit >= 1 || error("Arguments vertexLimit and edgeLimit should be at least 1. Received vertexLimit $vertexLimit and edgeLimit $edgeLimit.")
    length(fromGraphs) == length(toGraphs) || error("Arguments fromGraphs and toGraphs should be of equal lengths. fromGraphs had a length of $(length(fromGraphs)) and toGraphs had a length of $(length(toGraphs)).")
    # they should both be the same length
    for i in 1:length(fromGraphs)
        for j in 1:length(fromGraphs)
            if j == i
                continue
            end
            prod = apex(product(fromGraphs[i], add_loops(fromGraphs[j])))
            prod2 = apex(product(toGraphs[i], add_loops(toGraphs[j])))
            if length(vertices(prod)) < vertexLimit && length(edges(prod)) < edgeLimit && length(vertices(prod2)) < vertexLimit && length(edges(prod2)) < edgeLimit
                append!(fromGraphs, [prod])
                append!(toGraphs, [prod2])
            end
        end
    end
end

function lightShuffle(fromGraphs, toGraphs, vertexLimit, edgeLimit, intensity)
    vertexLimit >= 1 && edgeLimit >= 1 || error("Arguments vertexLimit and edgeLimit should be at least 1. Received vertexLimit $vertexLimit and edgeLimit $edgeLimit.")
    length(fromGraphs) == length(toGraphs) || error("Arguments fromGraphs and toGraphs should be of equal lengths. fromGraphs had a length of $(length(fromGraphs)) and toGraphs had a length of $(length(toGraphs)).")
    intensity < length(fromGraphs) || error("Argument intensity should be less than length of lists fromGraphs and toGraphs. Received intensity $intensity and list length $(length(fromGraphs)).")
    println("Shuffling...")
    #keep original list length since it will change
    original = length(toGraphs)
    total = length(toGraphs) * (intensity)
    count = 1
    for i in 1:original
        for j in 1:intensity
            num = rand(1:original)
            if num == i
                j = j - 1
                continue
            end
            println("Calculating $count of $total")
            count = count + 1
            prod = apex(product(fromGraphs[i], add_loops(fromGraphs[num])))
            prod2 = apex(product(toGraphs[i], add_loops(toGraphs[num])))
            if length(vertices(prod)) < vertexLimit && length(edges(prod)) < edgeLimit && length(vertices(prod2)) < vertexLimit && length(edges(prod2)) < edgeLimit
                append!(fromGraphs, [prod])
                append!(toGraphs, [prod2])
            end
        end
    end
end

# CAUTION: autoPlotAll is very slow!
# This checks every possible pair. Injection/Surjection isn't an accurate description for most
# pairs, but the data is still useful.
function autoPlotAll(fromList, toList)
    println("Autoplotting Homs...\nTotal pairs: $(length(toList) * length(toList))")
    x1 = Int64[]
    y1 = Float64[]
    x2 = Int64[]
    y2 = Float64[]
    x3 = Int64[]
    x4 = Int64[]
    count = 1
    for i in 1:length(fromList)
        f = fromList[i]
        for j in 1:length(toList)
            print("Graph pair $count:   ")
            t = toList[j]
            #injection
            append!(y1, time(median(@benchmark homomorphism($f, $t))))
            append!(x1, length(vertices(f)))
            append!(x3, length(edges(t)))
            print("Injection complete.   ")
            #surjection
            append!(y2, time(median(@benchmark homomorphism($t, $f))))
            append!(x2, length(vertices(t)))
            append!(x4, length(edges(t)))
            print("Surjection complete.\n")
            count = count + 1
        end
    end
    scatter([x1, x2], [y1, y2], title="Autoplotted Graph Vertices", xlabel="Number of \"From\" Vertices", ylabel="Single Hom Calculation Time (ns)", label=["Injective" "Surjective"])
    savefig("autoVertex.png")
    scatter([x3, x4], [y1, y2], title="Autoplotted Graph Edges", xlabel="Number of Edges", ylabel="Single Hom Calculation Time (ns)", label=["Injective" "Surjective"])
    savefig("autoEdge.png")
end