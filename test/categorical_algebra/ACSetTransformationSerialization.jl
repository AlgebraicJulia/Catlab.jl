using Test
using Catlab
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.CSets
import Catlab.CategoricalAlgebra.CSets: generate_json_acset, _parse_json_acset, parse_json_acset_transformation

using Catlab.Graphs

using DataStructures: OrderedDict
using JSON

g = @acset Graph begin
    V = 3
    E = 3
    src = [1,2,3]
    tgt = [2,3,1]
end

h = @acset Graph begin
    V = 4
    E = 5
    src = [1,2,3,3,2]
    tgt = [2,3,1,4,4]
end

gdict = generate_json_acset(g)
hdict = generate_json_acset(h)
ϕ = homomorphism(g,h, monic=true)
d = generate_json_acset(ϕ)

@testset "Dictionary Conversion" begin
@test d[:dom] == gdict
@test d[:codom] == hdict
@test collect(d[:transformation].V) == [1,2,3]
@test collect(d[:transformation].E) == [1,2,3]
end

# check that finfunctions just work.
@testset "Roundtrip" begin
    @test parse_json_acset_transformation(Graph, JSON.parse(JSON.json(generate_json_acset(ϕ)))) == ϕ
end

@testset "Attributes" begin
g = @acset WeightedGraph{Float64} begin
    V = 3
    E = 3
    src = [1,2,3]
    tgt = [2,3,1]
    weight = [1.2, 3, -1.8]
end

h = @acset WeightedGraph{Float64} begin
    V = 4
    E = 5
    src = [1,2,3,3,2]
    tgt = [2,3,1,4,4]
    weight = [1.2, 3, -1.8, 4,5]
end

gdict = generate_json_acset(g)
@test_skip JSON.json(gdict)
hdict = generate_json_acset(h)
ϕ = homomorphism(g,h, monic=true)
generate_json_acset(ϕ)
@test_skip JSON.json(generate_json_acset(ϕ))

@test_skip text = JSON.parse(JSON.json(generate_json_acset(ϕ)))
@test_skip _parse_json_acset_transformation(WeightedGraph, text) == ϕ
end