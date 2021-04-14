module TestACSetViews
using Test

using Catlab: @present, generator
using Catlab.Theories: compose, id
using Catlab.Graphs
using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.CategoricalAlgebra.ACSetViews
using Catlab.CategoricalAlgebra.CSets

using Tables

# Basic Indexing and Special Methods
####################################

@present TheoryLocatedGraph <: TheoryGraph begin
  Num::Data
  x::Attr(V,Num)
  y::Attr(V,Num)
end

const LocatedGraph = ACSetType(TheoryLocatedGraph)

g = @acset LocatedGraph{Float64} begin
  V = 5
  E = 4
  src = [1,1,1,1]
  tgt = [2,3,4,5]
  x = [0.,1.,0,-1.,0]
  y = [0.,0.,1.,0.,-1.]
end

edges = ACSetView(g,:E)

upward_edges = @select_where(edges, src.y <= tgt.y)
@test parts(upward_edges) == [1,2,3]

@test upward_edges[1,:src] == 1.
@test upward_edges[1,[:src,:x]] == 0.
@test upward_edges.src == [1,1,1]
@test upward_edges[:,[:tgt,:x]] == [1.,0.,-1.]

@test @compute_prop(upward_edges, (src.x - tgt.x)^2 + (src.y - tgt.y)^2) == [1,1,1]

# Tables.jl Interface
#####################

vertices = ACSetView(g,:V)

@test Tables.istable(vertices)
@test Tables.columnaccess(vertices)
@test Tables.columns(vertices) == vertices
@test Tables.columnnames(vertices) == (:x,:y)
@test Tables.getcolumn(vertices,:x)[2] == 1.
@test Tables.getcolumn(vertices,2,:x) == 1.

# Morphisms
###########

g = path_graph(WeightedGraph{Float64}, 2, E=(weight=2.0,))
h = path_graph(WeightedGraph{Float64}, 4, E=(weight=[1.,2.,3.],))
α = ACSetTransformation((V=[2,3], E=[2]), g, h)
αE = ACSetViewMorphism(α, :E)

@test is_natural(αE)
@test αE.f == α.components[:E]

end
