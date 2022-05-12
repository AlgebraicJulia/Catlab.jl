using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphs.GraphGenerators
include("SSets.jl")

# Graph Functions
# add_loops
add_loops!(g) = add_parts!(g, :E, nparts(g, :V), src=parts(g, :V), tgt=parts(g, :V))
add_loops(g) = begin
    h = copy(g)
    add_loops!(h)
    return h
end

"""Arguments g ang h of box_product are of type T where T is the super type for graphs."""
function box_product(g::T, h::T) where {T<:ACSet}
    g₀, h₀ = T(nv(g)), T(nv(h))
    incl_g = CSetTransformation((V=vertices(g), E=refl(g)), g₀, g)
    incl_h = CSetTransformation((V=vertices(h), E=refl(h)), h₀, h)
    proj_g₀, proj_h₀ = product(g₀, h₀)
    ob(pushout(pair(proj_g₀ ⋅ incl_g, proj_h₀),
        pair(proj_g₀, proj_h₀ ⋅ incl_h)))
end

# Acyclic Sparse V ≈ E or V = E
# Arranged in increasing vertex count.
# Naming scheme is based on vertex count.
a_sparse_three = @acset Graphs.Graph begin
    V = 3
    E = 3
    src = [1, 1, 2]
    tgt = [2, 3, 3]
end

a_sparse_four = @acset Graphs.Graph begin
    V = 4
    E = 4
    src = [1, 1, 2, 3]
    tgt = [2, 3, 4, 4]
end

a_sparse_five = @acset Graphs.Graph begin
    V = 5
    E = 5
    src = [1, 1, 2, 3, 4]
    tgt = [3, 5, 5, 5, 5]
end

a_sparse_six = @acset Graphs.Graph begin
    V = 6
    E = 6
    src = [1, 2, 3, 5, 6, 6]
    tgt = [2, 3, 5, 4, 3, 5]
end

a_sparse_six2 = @acset Graphs.Graph begin
    V = 6
    E = 6
    src = [3, 2, 2, 1, 4, 5]
    tgt = [2, 1, 4, 5, 6, 6]
end

a_sparse_seven = @acset Graphs.Graph begin
    V = 7
    E = 7
    src = [1, 3, 4, 5, 6, 6, 7]
    tgt = [4, 1, 2, 3, 3, 4, 2]
end

a_sparse_eight = @acset Graphs.Graph begin
    V = 8
    E = 8
    src = [1, 2, 2, 3, 4, 6, 7, 8]
    tgt = [2, 3, 5, 7, 2, 4, 8, 5]
end

a_sparse_eight2 = @acset Graphs.Graph begin
    V = 8
    E = 8
    src = [1, 1, 2, 3, 3, 3, 4, 4]
    tgt = [3, 4, 4, 2, 7, 8, 5, 6]
end

# Complete - Edge from each vertex to all other vertices.
# Arranged in increasing vertex count.
complete_list = Vector{Graph}()
for i in 1:10
    push!(complete_list, complete_graph(Graph, i))
end

loop_complete_list = Vector{Graph}()
for i in complete_list
    push!(loop_complete_list, add_loops(i))
end

# Directional checkerboard graphs - Acyclic
# Arranged in increasing vertex count.
# Naming scheme is based on graph vertex dimensions.
directional_box = @acset Graphs.Graph begin
    V = 4
    E = 4
    src = [1, 1, 2, 3]
    tgt = [2, 3, 4, 4]
end

directional_2x2 = @acset Graphs.Graph begin
    V = 9
    E = 12
    src = [1, 1, 2, 2, 3, 4, 4, 5, 5, 6, 7, 8]
    tgt = [2, 4, 3, 5, 6, 5, 7, 6, 8, 9, 8, 9]
end

# Linear (Path) Graphs
# Arranged in increasing vertex count.
# Naming scheme is based on vertex count.
line_two = @acset Graphs.Graph begin
    V = 2
    E = 1
    src = [1]
    tgt = [2]
end

line_three = @acset Graphs.Graph begin
    V = 3
    E = 2
    src = [1, 2]
    tgt = [2, 3]
end

line_four = @acset Graphs.Graph begin
    V = 4
    E = 3
    src = [1, 2, 3]
    tgt = [2, 3, 4]
end

line_five = @acset Graphs.Graph begin
    V = 5
    E = 4
    src = [1, 2, 3, 4]
    tgt = [2, 3, 4, 5]
end

line_six = @acset Graphs.Graph begin
    V = 6
    E = 5
    src = [1, 2, 3, 4, 5]
    tgt = [2, 3, 4, 5, 6]
end

line_seven = @acset Graphs.Graph begin
    V = 7
    E = 6
    src = [1, 2, 3, 4, 5, 6]
    tgt = [2, 3, 4, 5, 6, 7]
end

line_eight = @acset Graphs.Graph begin
    V = 8
    E = 7
    src = [1, 2, 3, 4, 5, 6, 7]
    tgt = [2, 3, 4, 5, 6, 7, 8]
end

#Undirected Path Graphs (can be used to generate undirected lattice/grid graphs)
# Arranged in increasing vertex count.
# Naming scheme is based on vertex count.
u_line_two = @acset Graphs.Graph begin
    V = 2
    E = 2
    src = [1, 2]
    tgt = [2, 1]
end

u_line_three = @acset Graphs.Graph begin
    V = 3
    E = 4
    src = [1, 2, 2, 3]
    tgt = [2, 3, 1, 2]
end

u_line_four = @acset Graphs.Graph begin
    V = 4
    E = 6
    src = [1, 2, 3, 2, 3, 4]
    tgt = [2, 3, 4, 1, 2, 3]
end

u_line_five = @acset Graphs.Graph begin
    V = 5
    E = 8
    src = [1, 2, 3, 4, 2, 3, 4, 5]
    tgt = [2, 3, 4, 5, 1, 2, 3, 4]
end

u_line_six = @acset Graphs.Graph begin
    V = 6
    E = 10
    src = [1, 2, 3, 4, 5, 2, 3, 4, 5, 6]
    tgt = [2, 3, 4, 5, 6, 1, 2, 3, 4, 5]
end

u_line_seven = @acset Graphs.Graph begin
    V = 7
    E = 12
    src = [1, 2, 3, 4, 5, 6, 2, 3, 4, 5, 6, 7]
    tgt = [2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6]
end

u_line_eight = @acset Graphs.Graph begin
    V = 8
    E = 14
    src = [1, 2, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 7, 8]
    tgt = [2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7]
end

# Generate larger graphs
large1 = apex(product(a_sparse_three, add_loops(a_sparse_four)))
large2 = apex(product(a_sparse_four, add_loops(a_sparse_five)))
large3 = apex(product(a_sparse_five, add_loops(a_sparse_six)))
large4 = apex(product(a_sparse_six, add_loops(a_sparse_six2)))
large5 = apex(product(a_sparse_six2, add_loops(a_sparse_seven)))
large6 = apex(product(a_sparse_seven, add_loops(a_sparse_eight)))
large7 = apex(product(a_sparse_eight, add_loops(a_sparse_eight2)))

# G larger than H for G->H
loop_large1 = add_loops(large1)
loop_large2 = add_loops(large2)
loop_large3 = add_loops(large3)
loop_large4 = add_loops(large4)
loop_sparse_three = add_loops(a_sparse_three)
loop_sparse_four = add_loops(a_sparse_four)
loop_sparse_five = add_loops(a_sparse_five)
loop_sparse_six = add_loops(a_sparse_six)
loop_sparse_seven = add_loops(a_sparse_seven)
loop_sparse_eight = add_loops(a_sparse_eight)

# H larger than G for G->H
loop_sparse_six2 = add_loops(a_sparse_six2)
loop_sparse_eight2 = add_loops(a_sparse_eight2)
loop_large5 = add_loops(large5)
loop_large6 = add_loops(large6)
loop_large7 = add_loops(large7)

# Simplicial Sets (n x n)
ss_four = repeat(4)
ss_five = repeat(5)
ss_six = repeat(6)
ss_seven = repeat(7)
ss_eight = repeat(8)

# Simplicial Sets (n x 1)
ss1d_four = repeat1d(4)
ss1d_five = repeat1d(5)
ss1d_six = repeat1d(6)
ss1d_seven = repeat1d(7)
ss1d_eight = repeat1d(8)

# Simplicial Set Lists
ss_list = [ss_four, ss_five, ss_six, ss_seven, ss_eight]
od_list = [ss1d_four, ss1d_five, ss1d_six, ss1d_seven, ss1d_eight]
quad_list = [ss_four, ss_five, ss_six, ss_seven, ss_eight, ss1d_four, ss1d_five, ss1d_six, ss1d_seven, ss1d_eight]