# __precompile__(false) #REMOVE
# ## Testing our parser
module ParserTests

using Test
using Catlab.ADTs.RelationTerm
using Catlab.Programs.RelationalPrograms
using Catlab.Parsers.RelationalParser


# Now we write some unit tests. This is how I wrote this code, by writing the tests from the bottom up.
@testset "Parens" begin
  @test lparen("(")[1] == "("
  @test rparen(")")[1] == ")"
  @test elname("R(a)")[1] == "R"
end

@testset "Arg" begin
  @test arg("x")[1] == Untyped(:x)
  @test arg("tgt=x")[1] == Kwarg(:tgt, Untyped(:x))
end

@testset "Args" begin
  @test args("x,y,z")[1] == [Untyped(:x), Untyped(:y), Untyped(:z)]
  @test args("tgt=x,src=y")[1] == [Kwarg(:tgt, Untyped(:x)), Kwarg(:src, Untyped(:y))]
end

@testset "Judgement" begin
  @test judgement("a:A,")[1] == Typed(:a, :A)
  @test judgement("ab:AB,")[1] == Typed(:ab, :AB)

  @test finjudgement("a:A")[1] == Typed(:a, :A)
  @test finjudgement("ab:AB")[1] == Typed(:ab, :AB)
end

@testset "judgements" begin
  @test judgements("a:A, b:B, c:C")[1] == [Typed(:a, :A), Typed(:b, :B), Typed(:c, :C)]
end

@testset "Outer Ports" begin
  @test outerPorts("(A)")[1] == [Untyped(:A)]
  @test outerPorts("(A,B)")[1] == [Untyped(:A), Untyped(:B)]
  @test outerPorts("(src=A, tgt=B)")[1] == [Kwarg(:src, Untyped(:A)), Kwarg(:tgt, Untyped(:B))]
end

@testset "Contexts" begin
  @test RelationalParser.context("(a:A,b:B)")[1] == [Typed(:a, :A), Typed(:b, :B)]
  @test RelationalParser.context("(a:A,  b:B)")[1] == [Typed(:a, :A), Typed(:b, :B)]
  @test RelationalParser.context("( a:A,  b:B )")[1] == [Typed(:a, :A), Typed(:b, :B)]
end

@testset "Statements" begin
  @test [Untyped(:u)] == [Untyped(:u)]
  @test statement("R(a,b)")[1] == Statement(:R, [Untyped(:a),Untyped(:b)])
  @test statement("S(u,b)")[1] == Statement(:S, [Untyped(:u),Untyped(:b)])
  @test statement("S(u,b,x)")[1].relation == Statement(:S, [Untyped(:u), Untyped(:b), Untyped(:x)]).relation
  @test statement("S(u,b,x)")[1].variables == Statement(:S, [Untyped(:u), Untyped(:b), Untyped(:x)]).variables
  @test statement("S(u)")[1].relation == Statement(:S, [Untyped(:u)]).relation
  @test statement("S(u)")[1].variables == Statement(:S, Var[Untyped(:u)]).variables
  @test statement("S(  a,    b  )")[1] == Statement(:S, [Untyped(:a),Untyped(:b)])
  @test statement("R(src=a, tgt=b)")[1] == Statement(:R, [Kwarg(:src, Untyped(:a)), Kwarg(:tgt, Untyped(:b))])
end

@testset "Body" begin
  @test body("""{
  R(a,b);}""")[1][1] isa Statement

  @test body("""{
  R(a,b);
  }""")[1][1] isa Statement

  @test body("""{
    R(a,b);
  }""")[1][1] isa Statement

  @test length(body("""{
  R(a,b);
    S(u,b);
  }""")[1]) == 2

  @test body("""{ R(a,b)\n S(u,b)\n}""")[1] == [Statement(:R, [Untyped(:a), Untyped(:b)]), Statement(:S, [Untyped(:u), Untyped(:b)])]
end

# Our final test shows that we can parse what we expect to be able to parse:
@testset "UWD" begin
  @test uwd("""{R(a,b); S(b,c);} where {a:A,b:B,c:C}""")[1].context == [Typed(:a, :A), Typed(:c,:C)]
  @test uwd("""{R(a,b); S(b,c);}
   where {a:A,b:B,c:C}""")[1].statements == [Statement(:R, [Typed(:a, :A), Typed(:b, :B)]),
    Statement(:S, [Typed(:b, :B), Typed(:c, :C)])]
  @test uwd("""{R(a,b); S(b,c);} where {a:A,b:B,c:C}""")[1] isa RelationTerm.UWDExpr
end

# Test Error Handling:

#Taken from "PEG.jl/blob/master/test/misc.jl" to test parsing exception handling
function parse_fails_at(rule, input)
  try
    parse_whole(rule, input)
    "parse succeeded!"
  catch err
    isa(err, Meta.ParseError) || rethrow()
    m = match(r"^On line \d+, at column \d+ \(byte (\d+)\):", err.msg)
    m == nothing && rethrow()
    parse(Int, m.captures[1])
  end
end

@testset "judgement_handling" begin
  @test parse_fails_at(judgement, "a:") == 3
  @test parse_fails_at(judgement, "a") == 2
end

@testset "context_handling" begin
  @test parse_fails_at(RelationalParser.context, "{a:A,b:B") == 9
  @test parse_fails_at(RelationalParser.context, "{a:A,b:B,") == 10
  @test parse_fails_at(RelationalParser.context, "{a:A,b:B,}") == 10
end

@testset "statement_handling" begin
  @test parse_fails_at(statement, "R(a,b") == 6
  @test parse_fails_at(statement, "R(a,b,") == 7
  @test parse_fails_at(statement, "R(a,b,)") == 7
  @test parse_fails_at(statement, "(a,b)") == 1
end

@testset "Line Handling" begin
  @test parse_fails_at(line, "R(a,b)") == 7
end

@testset "Body Handling" begin
  @test parse_fails_at(body, "{R(a,b)") == 8
  @test parse_fails_at(body, "R(a,b)}") == 1
end

# End-To-End Test Cases illustrating full on use of string macro
@testset "End-To-End" begin

  #Test "{R(x,y); S(y,z);}" where {x:X,y:Y,z:Z}
  parsed_result = relation"{R(x,y); S(y,z);} where {x:X,y:Y,z:Z}"
  
  v1 = Typed(:x, :X)
  v2 = Typed(:y, :Y)
  v3 = Typed(:z, :Z)
  c = [v1, v3]
  s = [Statement(:R, [v1,v2]),
    Statement(:S, [v2,v3])]
  u = UWDExpr(c, s)
  uwd_result = RelationTerm.construct(RelationDiagram, u)
  
  @test parsed_result == uwd_result

  # Test R(x, y); S(y, z); T(z, y, u) where {x:X, y:Y, z:Z, u:U}
  # Interesting Note: Context variables in this case are use to 
  # type variables and assign outer ports. 
  # While @relation may include u:U, we see it should be untyped so we leave it out
  # X and Z are the outer ports so they occur at the first and last indices of the context
  # Depending on design decisions, we may want to explicitly include the outer ports outside 
  # the context like @relation
  
  parsed_result = relation"""
  {
    R(x, y);
    S(y, z);
    T(z, y, u);
  } where {x:X, y:Y, z:Z}"""

  v1 = Typed(:x, :X)
  v2 = Typed(:y, :Y)
  v3 = Typed(:z, :Z)
  v4 = Untyped(:u)
  c = [v1, v3]
  s = [Statement(:R, [v1,v2]),
    Statement(:S, [v2,v3]),
    Statement(:T, [v3,v2, v4])]
  u = UWDExpr(c, s)
  uwd_result = RelationTerm.construct(RelationDiagram, u)

  @test parsed_result == uwd_result

end

end