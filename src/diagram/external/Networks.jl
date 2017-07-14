""" Add vertex/edge/graph properties to the basic graph types of LightGraphs.

Extracted from the Networks.jl package by Carlo Lucibello, which is no longer
actively maintained:
  https://github.com/JuliaGraphs/Networks.jl
"""
module Networks
export AbstractNetwork, Network, DiNetwork, ComplexNetworkNet
export setprop!, getprop, rmprop!, hasprop, graph

import Base: convert, promote_rule, ==, sort
using LightGraphs
import LightGraphs: Graph, DiGraph, SimpleGraph, Edge, fadj, nv, ne, edges,
  add_vertex!, add_vertices!, add_edge!, rem_edge!, rem_vertex!

# Here we should define a minimal interface
# One requirement could be the presence of
# a `graph` member, of type LightGraphs.Graph or DiGraph
abstract AbstractNetwork

nv(net::AbstractNetwork) = nv(net.graph)
ne(net::AbstractNetwork) = ne(net.graph)
edges(net::AbstractNetwork) = edges(net.graph)

# this is how one could define methods in LightGraphs
# to make everything work for types that embed a graph
fadj(g::Any) = fadj(convert(SimpleGraph, g))

"""
    `Network{V,E,H}`

`Network` is the core type for representing graphs with vertex and edge properties.
`G` is the type of the underlying graph; the vertex properties are of type `V`,
and the edge properties are of type `E`.
"""
type Network{V,E,H} <: AbstractNetwork
  graph::Graph
  vprops::Dict{Int, V}
  eprops::Dict{Edge, E}
  gprops::H
end

type DiNetwork{V,E,H} <: AbstractNetwork
  graph::DiGraph
  vprops::Dict{Int, V}
  eprops::Dict{Edge, E}
  gprops::H
end

typealias ComplexNetwork{V,E,H} Union{Network{V,E,H},DiNetwork{V,E,H}}

# convenience constructors for empty `Network`s with given types:
Network{V,E}(::Type{V}, ::Type{E}) = Network(Graph(), Dict{Int,V}(), Dict{Edge,E}(), Void())
Network{V}(::Type{V}) = Network(Graph(), Dict{Int,V}(), Dict{Edge,Void}(), Void())

Network{V,E}(g::Graph, ::Type{V}, ::Type{E}) = Network(g, Dict{Int,V}(), Dict{Edge,E}(), Void())
Network{V}(g::Graph, ::Type{V}) = Network(g, Dict{Int,V}(), Dict{Edge,Void}(), Void())
Network(g::Graph) = Network(g, Dict{Int,Void}(), Dict{Edge,Void}(), Void())

DiNetwork{V,E}(::Type{V}, ::Type{E}) = DiNetwork(DiGraph(), Dict{Int,V}(), Dict{Edge,E}(), Void())
DiNetwork{V}(::Type{V}) = DiNetwork(DiGraph(), Dict{Int,V}(), Dict{Edge,Void}(), Void())

DiNetwork{V,E}(g::DiGraph, ::Type{V}, ::Type{E}) = DiNetwork(g, Dict{Int,V}(), Dict{Edge,E}(), Void())
DiNetwork{V}(g::DiGraph, ::Type{V}) = DiNetwork(g, Dict{Int,V}(), Dict{Edge,Void}(), Void())

#### core functions ###########

function add_vertex!(g::ComplexNetwork)
    add_vertex!(g.graph)
    return nv(g)
end

function add_vertex!{V,E,H}(g::ComplexNetwork{V,E,H}, vprop::V)
    add_vertex!(g.graph)
    n = nv(g)
    g.vprops[n] = vprop
    return n
end

function add_vertices!{V,E,H}(g::ComplexNetwork{V,E,H}, vprops::Vector{V})
    for vprop in vprops
        add_vertex!(g, vprop)
    end
end

function add_edge!{V,E,H}(g::ComplexNetwork{V,E,H}, e::Edge, eprop::E)
    e = sort(g, e)
    g.eprops[e] = eprop
    return add_edge!(g.graph, e)
end

add_edge!(net::ComplexNetwork, i::Int, j::Int) = add_edge!(net.graph, i, j)
add_edge!(net::ComplexNetwork, e::Edge) = add_edge!(net.graph, e)
add_edge!{E}(net::ComplexNetwork, i::Int, j::Int, eprop::E) =
                                    add_edge!(net.graph, Edge(i,j), eprop)

function rem_edge!(n::ComplexNetwork, e::Edge)
    e = sort(n, e)
    delete!(n.eprops, e)
    rem_edge!(n.graph, e)
end

rem_edge!(n::ComplexNetwork, i::Int, j::Int) = rem_edge!(n, Edge(i,j))

"""
    rem_vertex!(g, v)

Remove the vertex `v` from graph `g`.
This operation has to be performed carefully if one keeps external data structures indexed by
edges or vertices in the graph, since internally the removal is performed swapping the vertices `v`  and `n=nv(g)`,
and removing the vertex `n` from the graph.
After removal the vertices in the ` g` will be indexed by 1:n-1.
This is an O(k^2) operation, where `k` is the max of the degrees of vertices `v` and `n`.
Returns false if removal fails (e.g., if vertex is not in the graph); true otherwise.
"""
function rem_vertex!(net::ComplexNetwork, v::Int)
    g = net.graph
    v in vertices(g) || return false
    n = nv(g)

    edgs = in_edges(g, v)
    for e in edgs
        rem_edge!(net, e)
    end

    neigs = copy(in_neighbors(g, n))
    for i in neigs
        rem_edge!(g, Edge(i, n))
    end
    if v != n
        for i in neigs
            eold = Edge(i, n)
            enew = Edge(i, v)
            add_edge!(g, enew)
            if hasprop(net, eold)
                ep = getprop(net, eold)
                rmprop!(net, eold)
                setprop!(net, enew, ep)
            end
        end
    end

    if is_directed(g)
        edgs = out_edges(g, v)
        for e in edgs
            rem_edge!(net, e)
        end
        neigs = copy(out_neighbors(g, n))
        for i in neigs
            rem_edge!(g, Edge(n, i))
        end
        if v != n
            for i in neigs
                eold = Edge(n,i)
                enew = Edge(v,i)
                add_edge!(g, enew)
                if hasprop(net, eold)
                    ep = getprop(net, eold)
                    rmprop!(net, eold)
                    setprop!(net, enew, ep)
                end
            end
        end
    end

    if hasprop(net, n)
        p = getprop(net, n)
        rmprop!(net, n)
        setprop!(net, v, p)
    end
    g.vertices = 1:n-1
    pop!(g.fadjlist)
    if is_directed(g)
        pop!(g.badjlist)
    end
    return true
end

### properties setters and getters

function setprop!{V,E,H}(net::ComplexNetwork{V,E,H}, i::Int, vprop::V)
    net.vprops[i] = vprop
end


getprop(net::ComplexNetwork, i::Int) = net.vprops[i]
getprop(net::ComplexNetwork, e::Edge) = (e = sort(net, e); net.eprops[e])
getprop(net::ComplexNetwork, i::Int, j::Int) = getprop(net, Edge(i,j))

function setprop!{V,E,H}(net::ComplexNetwork{V,E,H}, e::Edge, eprop::E)
    e = sort(net, e)
    net.eprops[e] = eprop
end
setprop!{V,E,H}(net::ComplexNetwork{V,E,H}, i::Int, j::Int, eprop::E) =
                                                setprop!(net, Edge(i,j), eprop)


function rmprop!(net::ComplexNetwork, i::Int)
    delete!(net.vprops, i)
end

function rmprop!(net::ComplexNetwork, e::Edge)
    e = sort(net, e)
    delete!(net.eprops, e)
end

rmprop!(net::ComplexNetwork, i::Int, j::Int) = rmprop!(net, Edge(i,j))

hasprop(net::ComplexNetwork, i::Int) = haskey(net.vprops, i)
hasprop(net::ComplexNetwork, e::Edge) = (e=sort(net, e); haskey(net.eprops, e))
hasprop(net::ComplexNetwork, i::Int, j::Int) = hasprop(net, Edge(i,j))


==(n::ComplexNetwork, m::ComplexNetwork) = (n.graph == m.graph) && (n.vprops == m.vprops) && (n.eprops == m.eprops)
# Integration with LightGraphs package

sort(g::Network, e::Edge) = e[1] <= e[2] ? e : reverse(e)
sort(g::DiNetwork, e::Edge) = e
graph(net::ComplexNetwork) = net.graph

function convert{T<:SimpleGraph, V,E,H}(::Type{T}, net::ComplexNetwork{V,E,H})
    if typeof(net.graph) <: T
        return net.graph
    else
        error("Cannot convert network $T to graphtype $T")
    end
end

# promotion_rule{T<:SimpleGraph}(::Type{T}, ::Type{Network}) = T
promote_rule{Graph,V,E,H}(::Type{Network{V,E,H}}, ::Type{Graph}) = Graph
promote_rule{DiGraph,V,E,H}(::Type{DiNetwork{V,E,H}}, ::Type{DiGraph}) = DiGraph

end
