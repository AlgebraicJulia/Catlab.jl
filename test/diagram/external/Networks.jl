module TestNetworks
using Base.Test

using LightGraphs
using Catlab.Diagram.Networks

g = Graph(5)
dg = DiGraph(5)
function prepgraph(g)
    add_edge!(g, 1,2)
    add_edge!(g, 2,3)
    add_edge!(g, 3,4)
    add_edge!(g, 4,5)
    add_edge!(g, 5,1)
    if is_directed(g)
        net = DiNetwork(g, Dict{Int, Float64}(), Dict{Edge, Float64}(), Void())
    else
        net = Network(g, Dict{Int, Float64}(), Dict{Edge, Float64}(), Void())
    end
    net.eprops[Edge(5, 1)] = 2.3
    return net
end

g = Graph()
add_vertex!(g)
add_vertex!(g)
add_edge!(g, 1, 2)

net = Network(String)
add_vertex!(net, "a")
add_vertex!(net, "b")
add_edge!(net, 1, 2)

@test net.graph == g
@test net.vprops[1] == "a"
@test net.vprops[2] == "b"

@test typeof(net.vprops) <: Dict
@test typeof(net.eprops) <: Dict

@test nv(net) == nv(net.graph)
@test ne(net) == ne(net.graph)

net2 = Network(g, String)
setprop!(net2, 1, "a")
setprop!(net2, 2, "b")
@test net2 == net
@test getprop(net2, 1) == "a"
@test getprop(net2, 2) == "b"

net3 = Network(g, Void, String)
@test nv(g) == 2
add_vertex!(net3)
@test nv(g) == 3
@test nv(net3) == 3

setprop!(net3, Edge(2,1), "ciao")
@test net3.eprops[Edge(1,2)] == "ciao"

rem_edge!(net3, 1 , 2)
@test ne(net3) == 0
add_edge!(net3, 2, 1)
@test ne(net3) == 1
rem_edge!(net3, Edge(1 , 2))
@test ne(net3) == 0
add_edge!(net3, Edge(1, 2))
@test ne(net3) == 1
@test_throws KeyError getprop(net3, Edge(1,2))

setprop!(net3, 3, 2, "ciao")
@test getprop(net3, Edge(2,3)) == "ciao"
@test getprop(net3, Edge(3,2)) == "ciao"

rmprop!(net3, 3, 2)
@test_throws KeyError getprop(net3, 3,2)

@test Graph(net3) == net3.graph
@test graph(net3) == net3.graph

n = Network(CompleteGraph(5), Dict{Symbol,Any}, Dict{Symbol,Any})
for i=1:5
    @test hasprop(n, i) == false
end
for e in edges(g)
    @test hasprop(n, src(e), dst(e)) == false
end
setprop!(n, 2, Dict{Symbol,Any}(:lab=>"a"))
@test hasprop(n, 2) == true
@test nv(n) == 5
@test ne(n) == 10
rmprop!(n, 2)
@test hasprop(n, 2) == false

## remove vertex test
rem_vertex!(n, 2)
@test nv(n) == 4
for i=1:5
    @test hasprop(n, i) == false
end
add_vertex!(n, Dict{Symbol,Any}(:lab=>"a"))
setprop!(n, 1, Dict{Symbol,Any}(:lab=>"a"))
setprop!(n, 1,2, Dict{Symbol,Any}(:lab=>"aa"))
@test nv(n) == 5
rem_vertex!(n,5)
@test getprop(n, 1) == Dict(:lab=>"a")
@test getprop(n, 1,2) == Dict(:lab=>"aa")
@test nv(n) == 4
for i=2:4
    @test hasprop(n, i) == false
end

rem_vertex!(n,4)
@test getprop(n, 1) == Dict(:lab=>"a")
@test getprop(n, 1,2) == Dict(:lab=>"aa")
@test nv(n) == 3
for i=2:3
    @test hasprop(n, i) == false
end

end
