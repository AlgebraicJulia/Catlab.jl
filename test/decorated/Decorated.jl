using Test
using Catlab
using Catlab.CategoricalAlgebra
import Catlab.CategoricalAlgebra.Limits: CompositePushout
using Catlab.Decorated

f = FinFunction([1,2], 3)
g = FinFunction([1,2], 3)

h = FinFunction([1,2], 3)
p = pushout(f,g);
p3 = pushout([f,g,h]);

@testset "Structure" begin
  @test codom(p.coeq.cocone.legs[1]) == apex(p)
  @test collect(p.coeq.cocone.legs[1]) == [1,2,3,1,2,4]
  @test reduce(vcat, [[1,2,3],[1,2,4]]) == [1,2,3,1,2,4]
  @test typeof(p) <: CompositePushout
end

@testset "Gluing" begin
  @test glue(Vect, p, [[1,2,3],[1,2,4]]) == [2,4,3,4]
  @test glue(Vect, p3, [[1,2,3],[1,2,4],[1,2,5]]) == [3,6,3,4,5]
end

@testset "DecoratedCorelations" begin
  f₁ = VectCospan([1,2,3], Cospan(FinFunction([1], 3), FinFunction([1,2],3)))
  f₂ = VectCospan([1,2,4], Cospan(FinFunction([1,2], 3), FinFunction([2],3)))
  # @show f₁
  @test glue(SummationProjection, f₁,f₂) == [2,4]
  f₁ = VectCospan([1,2,3], Cospan(FinFunction([1,2], 3), FinFunction([1,2],3)))
  f₂ = VectCospan([1,2,4], Cospan(FinFunction([1,2], 3), FinFunction([2,3],3)))
  @test glue(SummationProjection, f₁,f₂)  == [2,4,4]
  # Don't know how to do multi-arity corelations yet.
  # glue(SummationProjection, p3, [[1,2,3],[1,2,4],[1,2,5]]) == [3,6,3,4,5]
  # p4 = pushout(FinFunction([1,2], 4), FinFunction([1,2],4))
  # glue(SummationProjection, p4, [[1,2,3,4],[1,2,3,4]])# == [2,4]
end