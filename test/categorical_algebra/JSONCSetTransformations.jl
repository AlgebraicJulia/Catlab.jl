# FinFunction serialization
###########################
function roundtrip_json_fin_function(f::T) where T <: FinFunction
  mktempdir() do dir
    path = joinpath(dir, "fin_function.json")
    write_json_fin_function(f, path)
    read_json_fin_function(path)
  end
end

f = FinFunction([2,3], 2, 4)
g = FinFunction([2],   1, 3)

for ϕ in [f,g]
  @test roundtrip_json_fin_function(ϕ) == ϕ
end

# ACSetTransformation serialization
###################################

function roundtrip_json_acset_transformation(x::T) where T <: ACSetTransformation
  mktempdir() do dir
    path = joinpath(dir, "acset_transformation.json")
    write_json_acset_transformation(x, path)
    read_json_acset_transformation(T, path)
  end
end

g = path_graph(WeightedGraph{Float64}, 2, E=(weight=2,))
h = path_graph(WeightedGraph{Float64}, 4, E=(weight=[1,2,3],))
α = ACSetTransformation((V=[2,3], E=[2]), g, h)
@test_broken roundtrip_json_acset_transformation(g) == g

