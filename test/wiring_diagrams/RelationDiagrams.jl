module TestRelationDiagrams

using Test

using GATlab
using Catlab.CategoricalAlgebra.CSets
using Catlab.UndirectedWiringDiagrams
using Catlab.RelationDiagrams 

@testset "Constructor Call" begin
  # Untyped Unnamed Relation Diagram
  uwd = RelationDiagram(3, port_names=nothing)
  @test uwd isa RelationDiagrams.UntypedUnnamedRelationDiagram

  # Untyped Unnamed Relation Diagram
  uwd = RelationDiagram(3, port_names=[:a, :b, :c])
  @test uwd isa RelationDiagrams.UntypedNamedRelationDiagram

  # Typed Unnamed Relation Diagram
  uwd = RelationDiagram([:X, :Y, :Z], port_names=nothing)
  @test uwd isa RelationDiagrams.TypedUnnamedRelationDiagram

  # Typed Named Relation Diagram
  uwd = RelationDiagram([:X, :Y, :Z], port_names=[:a, :b, :c])
  @test uwd isa RelationDiagrams.TypedNamedRelationDiagram
end

end