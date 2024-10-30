module TestGATlabUpstream 
using GATlab, Catlab, Test

using .ThCategory

# Test default model 
@test_throws MethodError id(2)

Catlab.Theories.@default_model ThCategory{Int, Vector{Int}} [model::FinSetC]

@test id(2) == [1,2]
@test compose([1,2,3], [2,1,3]) == [2,1,3]

struct FSC <: Model{Tuple{Int, Vector{Int}}}
end

Catlab.Theories.@default_model ThCategory{Int, Vector{Int}} FinSetC=>FSC

@test id[FSC()](2) == [1,2]

# Test symbolic model

abstract type CategoryExpr{T} <: GATExpr{T} end

abstract type ObExpr{T} <: CategoryExpr{T} end

abstract type HomExpr{T} <: CategoryExpr{T} end

Catlab.Theories.@symbolic_model FreeCategory{ObExpr, HomExpr} ThCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g), ThCategory.id)
end

M = FreeCategory.Meta.M() 
@test M isa GATlab.Models.SymbolicModels.Model{Tuple{FreeCategory.Ob, FreeCategory.Hom}}
x, y = FreeCategory.Ob{:generator}([:x], []), FreeCategory.Ob{:generator}([:y], [])
f = FreeCategory.Hom{:generator}([:f], [x, y])

@test ThCategory.id[M](x) isa HomExpr{:id}

end # module 
