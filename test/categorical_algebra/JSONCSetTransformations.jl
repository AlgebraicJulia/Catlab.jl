module TestJSONCSetTransformations
using Test

using Catlab.CategoricalAlgebra, Catlab.Graphs

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

function roundtrip_json_acset_transformation(x, t)
  mktempdir() do dir
    path = joinpath(dir, "acset_transformation.json")
    write_json_acset_transformation(x, path)
    read_json_acset_transformation(t, path)
  end
end

g = path_graph(WeightedGraph{Float64}, 2, E=(weight=2,))
h = path_graph(WeightedGraph{Float64}, 4, E=(weight=[1,2,3],))
α = ACSetTransformation((V=[2,3], E=[2]), g, h)
@test roundtrip_json_acset_transformation(α, WeightedGraph{Float64}) == α

@present SchFalseDecapode(FreeSchema) begin
  (Var, TVar, Op1, Op2)::Ob
  (Type, Operator)::AttrType
  src::Hom(Op1, Var)
  tgt::Hom(Op1, Var)
  proj1::Hom(Op2, Var)
  proj2::Hom(Op2, Var)
  res::Hom(Op2, Var)
  incl::Hom(TVar, Var)
  
  op1::Attr(Op1, Operator)
  op2::Attr(Op2, Operator)
  type::Attr(Var, Type)

  Name::AttrType
  name::Attr(Var, Name)

  (Σ, Summand)::Ob
  summand::Hom(Summand, Var)
  summation::Hom(Summand, Σ)
  sum::Hom(Σ, Var)
end

@acset_type FalseDecapode(SchFalseDecapode,
  index=[:src, :tgt, :res, :incl, :op1, :op2, :type])

dynamics = @acset FalseDecapode{Symbol,Symbol,Symbol} begin
  Var = 2
  name = [:Q, :Qᵤ]
  type = [:Form0, :Form0]
  Op1 = 2
  src = [1,1]
  tgt = [2,2]
  op1 = [:dt,:Δ]
  TVar = 1
  incl = [2]
end
boundaries = @acset FalseDecapode{Symbol,Symbol,Symbol} begin
  Var = 1
  name = [:Q]
  type = [:Form0]
end

boundary_conditions = ACSetTransformation(
  (Var=[1],),
  boundaries, dynamics)

@test roundtrip_json_acset_transformation(boundary_conditions,
  FalseDecapode{Symbol,Symbol,Symbol}()) == boundary_conditions

end

