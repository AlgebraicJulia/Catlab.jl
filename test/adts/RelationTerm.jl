""" Relation Term Tests

The following module checks that the RelationTerm ADT successfully constructs
ACSet representation. 
"""
module RelationTermTests

using Test
using Catlab.ADTs.RelationTerm
using Catlab.WiringDiagrams.UndirectedWiringDiagrams
using Catlab.Programs.RelationalPrograms


@testset "UWD Construction" begin
  # parsed = @relation (x,z) where (x,y,z) begin
  # R(x,y)
  # S(y,z)
  # end

  v1 = Untyped(:x)
  v2 = Untyped(:y)
  v3 = Untyped(:z)
  c = [v1, v2, v3]
  op = [v1, v3]
  s = [Statement(:R, [v1, v2]), Statement(:S, [v2, v3])]
  u = UWDExpr(op, c, s)

  # ADT Based Construction
  uwd_result = RelationTerm.construct(RelationDiagram, u)
  
  #ACSet Creation
  d = RelationDiagram(2)
  add_box!(d, 2, name=:R); add_box!(d, 2, name=:S)
  add_junctions!(d, 3, variable=[:x,:y,:z])
  set_junction!(d, [1,2,2,3]) #Understanding: Port 1 connects to 1, port 2 to 2, port 3 to 2, port 4 to 3
  set_junction!(d, [1,3], outer=true)

  #Test Equality
  @test uwd_result == d

  # parsed = @relation (x,y,z) where (x::X, y::Y, z::Z, w::W) begin
  # R(x,w)
  # S(y,w)
  # T(z,w)
  # end

  v1 = Typed(:x, :X)
  v2 = Typed(:y, :Y)
  v3 = Typed(:z, :Z)
  v4 = Typed(:w, :W)
  c = [v1, v2, v3, v4]
  op = [v1, v2, v3]
  s = [Statement(:R, [v1, v4]), Statement(:S, [v2, v4]), Statement(:T, [v3, v4])]
  u = UWDExpr(op, c, s)

  uwd_result = RelationTerm.construct(RelationDiagram, u)

  d = RelationDiagram([:X,:Y,:Z])
  add_box!(d, [:X,:W], name=:R)
  add_box!(d, [:Y,:W], name=:S)
  add_box!(d, [:Z,:W], name=:T)
  add_junctions!(d, [:X,:Y,:Z,:W], variable=[:x,:y,:z,:w])
  set_junction!(d, [1,4,2,4,3,4])
  set_junction!(d, [1,2,3], outer=true)
  @test uwd_result == d
end

end

# TODO: Update Show function in RelationTerm to work with new outer ports
# TODO: need to bring the implementation of construct into compliance with existing catlab impl.
# TODO: add outer ports to UWDExpr and then to the construct function
# TODO: add outer ports to parser
# TODO; relation macro should emit a RelationTerm instead of using the PEG Parser.
# TODO: refactor the lexer out of the parser and make those reusable.