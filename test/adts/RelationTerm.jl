""" Relation Term Tests

The following module checks that the RelationTerm ADT successfully constructs
ACSet representation. 
"""
module RelationTermTests

using Test
using Catlab
using Catlab.ADTs.RelationTerm
using Catlab.WiringDiagrams.UndirectedWiringDiagrams
using Catlab.Programs.RelationalPrograms


#@testset "UWD Construction" begin
  # parsed = @relation (x,z) where (x,y,z) begin
  # R(x,y)
  # S(y,z)
  # end

  # TODO: need to bring the implementation of construct into compliance with existing catlab impl.
  # TODO: add outer ports to UWDExpr and then to the construct function
  # TODO: add outer ports to parser
  # TODO; relation macro should emit a RelationTerm instead of using the PEG Parser.
  # TODO: refactor the lexer out of the parser and make those reusable.

  v1 = Untyped(:x)
  v2 = Untyped(:y)
  v3 = Untyped(:z)
  c = [v1, v3]
  # Idea: c = [v1, v2, v3]
  # idea: op = [v1, v3]
  s = [Statement(:R, [v1, v2]), Statement(:S, [v2, v3])]
  u = UWDExpr(c, s)
  # Idea: u = UWDExpr(op, c, s)

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
  d

  
  #end

end