using Catlab
import Graphs as grs
import Catlab.Graphs as cat_grs 
import Catlab.Graphics: Graphviz
using Catlab.Graphics, Catlab.CategoricalAlgebra, Catlab.Graphics.GraphvizGraphs
using LinearAlgebra
using ..Visualization
using NLsolve
using Random

# TO ADD: ideal path vs shortest path
# look into figuring out how to specify rotation (think square) 
# need right angles for squares and one right angle for triangle

# graph generators - Owen


#======= file I/O to get positions =======#

#=
function get_positions(g)
    to_graphviz(prog="dot", g)
end
=#

#======= create weighted laplacian =======#
function weighted_laplacian(g, num_vert)
    # calculate shortest distance
    weighted_lap = - grs.floyd_warshall_shortest_paths(g).dists
    the_sum = sum(weighted_lap)

    # check for i = j
    n = num_vert
    for i in 1:n
        for j in 1:n
            if(weighted_lap[i,j] == 0)
                weighted_lap[i,j] = the_sum
            end
        end
    end
    
    return weighted_lap
end

#current pos is vector of positions (x,y)

#======= create X(t) laplacian =======#
function x_laplacian(g, current_pos, num_vert)
    n = num_vert
    x_lap = zeros(n,n)
    # might want to change floyd warshall to something else - meant to be the IDEAL path
    dist = grs.floyd_warshall_shortest_paths(g).dists

    for i in 1:n
        current = current_pos[i]
        
        if(i == n) 
            neighbor = current_pos[i-1]
        else
            neighbor = current_pos[i+1]
        end

        for j in 1:n
            if(i != j)
                # node i is located at Xi
                # confused on the x,y of positions --- FIX THIS
                x_lap[i,j] = -1 * dist[i,j] * inv(norm(current - neighbor))
            end
        end
    end

    the_sum = sum(x_lap)

    #find zeros
    for i in n
        for j in n
            if(x_lap[i,j] == 0)
                x_lap[i,j] = -1 * the_sum
            end
        end
    end

    return x_lap
end

#current_pos is vector of positions (x,y)

#======= create stress function =======#
function stress_function(graph, current_pos, num_vert)
    stress = []

    # constant, calculate once
    w_lap = weighted_laplacian(graph, num_vert)
    n = num_vert

    # recomputed at every iteration (bc it includes position)
    x_lap = x_laplacian(graph, current_pos, num_vert)

    #equation
    (x, y) -> (inv(weighted_lap[i,j]) * x_lap[i,j] * x)
    new_pos = 0;

    for i in 1:n
        current = current_pos[i]
        for j in 1:n

            function f!(F, x)
                F[1] = (inv(w_lap[i,j]) * x_lap[i,j] * x[1])
                F[2] = (inv(w_lap[i,j]) * x_lap[i,j] * x[2])
            end
            new_pos = nlsolve(f!, current)
        end
        push!(stress, new_pos.zero)
    end

    return stress
end

# current_pos is vector of positions (vector of vectors?)

#======= calculate for all nodes =======#
function stress_majorization(original_pos, old_graph, num_vert)
    n = num_vert
    new_positions = Vector{String}()

    #end when [stress(X(t)) - stress(X(t+1))] / stress(X(t)) < 10^-4

    #gives a vector of NL solve results
    original_stress = stress_function(old_graph, original_pos, n)

    new_graph = old_graph
    new_pos = original_pos
    current_stress = original_stress

    # FIX ME!!!!! while loop broken
    #while((original_stress[n][1] - current_stress[n][1]) / original_stress[n][1] < 10^(-4))
    #for i in 1:2
       
    empty!(new_positions)

    # gives a vector of (x,y) vectors
    stress = stress_function(new_graph, new_pos, n)
    new_pos = stress

    for i in 1:n
        #gives the solution vector (x,y)
        sln = new_pos[i]
        string_sln = string(sln[1], ",", sln[2])

        push!(new_positions, string_sln)
    end


    return new_positions
end


#======= TESTING =======#


#original graph

nv = 4

cat_g = cat_grs.cycle_graph(cat_grs.Graph, nv)
gv = to_graphviz(cat_g)

g = grs.cycle_graph(nv)

# new graph

#good guess
#curr = [[1.0, 0.0], [2.0, 1.0], [3.0, 1.0], [4.0, 1.0], [5.0, 0.0]]

curr = []
#bad guess
for i in 1:nv
    push!(curr, [float(rand((1:nv))), float(rand((0:nv)))])
end

pos_string = stress_majorization(curr, g, nv)

new_G = to_graphviz_property_graph(cat_g; prog="neato", node_attrs=Dict(:pos=>pos_string))
#new_G = to_graphviz_property_graph(cat_g; prog="neato")

to_graphviz(new_G)

