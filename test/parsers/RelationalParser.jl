### Testing our parser
module ParserTests

using Test
using Catlab.ADTs.RelationTerm
using Catlab.Parsers.ParserCore
using Catlab.Parsers.RelationalParser
using Catlab.WiringDiagrams.UndirectedWiringDiagrams
using Catlab.WiringDiagrams.RelationDiagrams
using Catlab.CategoricalAlgebra.CSets
 


# Now we write some unit tests. This is how I wrote this code, by writing the tests from the bottom up.
@testset "Parens" begin
  @test lparen("(")[1] == "("
  @test rparen(")")[1] == ")"
  @test ident("R(a)")[1] == "R"
end

@testset "Arg" begin
  @test arg("x")[1] == Untyped(:x)
  @test arg("tgt=x")[1] == Kwarg(:tgt, Untyped(:x))
end

@testset "Args" begin
  @test args("x,y,z")[1] == [Untyped(:x), Untyped(:y), Untyped(:z)]
  @test args("tgt=x,src=y")[1] == [Kwarg(:tgt, Untyped(:x)), Kwarg(:src, Untyped(:y))]
  @test args("")[1] == []
end

@testset "Judgement" begin
  @test judgement("a:A")[1] == Typed(:a, :A)
  @test judgement("ab:AB")[1] == Typed(:ab, :AB)

  @test judgement("a")[1] == Untyped(:a)
end

@testset "judgements" begin
  @test judgements("a:A, b:B, c:C")[1] == [Typed(:a, :A), Typed(:b, :B), Typed(:c, :C)]
  @test judgements("a, b, c")[1] == [Untyped(:a), Untyped(:b), Untyped(:c)]
  @test judgements("")[1] == []
  @test judgements("a:1, b:2")[1] == [Typed(:a, 1), Typed(:b, 2)]
  @test judgements("a:n(1), b:n(2)")[1] == [Typed(:a, Expr(:n, 1)), Typed(:b, Expr(:n, 2))]
end

@testset "Outer Ports" begin
  @test outerPorts("(A)")[1] == [Untyped(:A)]
  @test outerPorts("(A,B)")[1] == [Untyped(:A), Untyped(:B)]
  @test outerPorts("(src=A, tgt=B)")[1] == [Kwarg(:src, Untyped(:A)), Kwarg(:tgt, Untyped(:B))]
  @test outerPorts("()")[1] == []
end

@testset "Contexts" begin
  @test RelationalParser.context("(a:A,b:B)")[1] == [Typed(:a, :A), Typed(:b, :B)]
  @test RelationalParser.context("(a:A,  b:B)")[1] == [Typed(:a, :A), Typed(:b, :B)]
  @test RelationalParser.context("( a:A,  b:B )")[1] == [Typed(:a, :A), Typed(:b, :B)]
  @test RelationalParser.context("(x,y)")[1] == [Untyped(:x), Untyped(:y)]
  @test RelationalParser.context("()")[1] == []
end

PEG.setdebug!(false) # DEBUG

@testset "Expr" begin
  @test expr("n(1)")[1] == Expr(:n, 1)
  @test expr("n(1,2)")[1] == Expr(:n, 1, 2)
  @test expr("1")[1] == 1
  @test expr("hii")[1] == :hii
end

@testset "Expression Typed Context" begin
  @test RelationalParser.context("(a:n(1), b:n(2))")[1] == [Typed(:a, Expr(:n, 1)), Typed(:b, Expr(:n, 2))]
  @test RelationalParser.context("(a:1, b:2)")[1] == [Typed(:a, 1), Typed(:b, 2)]
  @test RelationalParser.context("(a:hii, b:hello)")[1] == [Typed(:a, :hii), Typed(:b, :hello)]
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
  @test uwd("""(x,z) where (x,y,z) {R(x,y); S(y,z);}""")[1].context == [Untyped(:x), Untyped(:y), Untyped(:z)]
  @test uwd("""(x,z) where (x,y,z)
    {R(x,y); S(y,z);}""")[1].statements == [Statement(:R, [Untyped(:x), Untyped(:y)]),
    Statement(:S, [Untyped(:y), Untyped(:z)])]
  @test uwd("""(x,z) where (x,y,z) {R(x,y); S(y,z);}""")[1] isa RelationTerm.UWDExpr
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
  @test parse_fails_at(judgement, ":a") == 1
end

@testset "context_handling" begin
  @test parse_fails_at(RelationalParser.context, "(a:A,b:B") == 9
  @test parse_fails_at(RelationalParser.context, "(a:A,b:B,") == 10
  @test parse_fails_at(RelationalParser.context, "(a:A,b:B,)") == 10
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
  parsed_result = relation"() where (x:X,y:Y,z:Z) {R(x,y); S(y,z);}"
  
  v1 = Typed(:x, :X)
  v2 = Typed(:y, :Y)
  v3 = Typed(:z, :Z)
  op = []
  c = [v1, v2, v3]
  s = [Statement(:R, [v1,v2]),
    Statement(:S, [v2,v3])]
  u = UWDExpr(op, c, s)
  uwd_result = RelationTerm.construct(RelationDiagram, u)
  
  @test parsed_result == uwd_result

  # Untyped
  #--------

  parsed = relation"(x,z) where (x,y,z) {R(x,y); S(y,z);}"

  d = RelationDiagram(2)
  add_box!(d, 2, name=:R); add_box!(d, 2, name=:S)
  add_junctions!(d, 3, variable=[:x,:y,:z])
  set_junction!(d, [1,2,2,3]) #Understanding: Port 1 connects to 1, port 2 to 2, port 3 to 2, port 4 to 3
  set_junction!(d, [1,3], outer=true)
  @test parsed == d

  # Abbreviated syntax where context is inferred.
  d1 = relation"(x,y,z) where () {R(x,y); S(y,z);}"
  d2 = relation"(x, y, z) where (x,y,z) {R(x,y); S(y,z);}"
  @test d1 == d2

  # Special case: closed diagram.
  parsed = relation"() where (a) {R(a,a);}"
  d = RelationDiagram(0)
  add_box!(d, 2, name=:R)
  add_junction!(d, variable=:a); set_junction!(d, [1,1])
  @test parsed == d

  parsed = relation"() where () {A();}"
  d = RelationDiagram(0)
  add_box!(d, 0, name=:A)
  @test parsed == d


  # Typed by Symbols
  #------

  parsed = relation"(x,y,z) where (x:X, y:Y, z:Z, w:W) {
  R(x,w);
  S(y,w);
  T(z,w);}" #Only allows for ; or \n but not ;\n
  d = RelationDiagram([:X,:Y,:Z])
  add_box!(d, [:X,:W], name=:R)
  add_box!(d, [:Y,:W], name=:S)
  add_box!(d, [:Z,:W], name=:T)
  add_junctions!(d, [:X,:Y,:Z,:W], variable=[:x,:y,:z,:w])
  set_junction!(d, [1,4,2,4,3,4])
  set_junction!(d, [1,2,3], outer=true)
  @test parsed == d


  # Typed by Integers
  #------

  parsed = relation"(x,y,z) where (x:1, y:2, z:3, w:4) {
  R(x,w);
  S(y,w);
  T(z,w);}"

  d = RelationDiagram([:1,:2,:3])
  add_box!(d, [:1,:4], name=:R)
  add_box!(d, [:2,:4], name=:S)
  add_box!(d, [:3,:4], name=:T)
  add_junctions!(d, [:1,:2,:3,:4], variable=[:x,:y,:z,:w])
  set_junction!(d, [1,4,2,4,3,4])
  set_junction!(d, [1,2,3], outer=true)
  @test parsed == d



  # Typed by Expressions
  #------

  parsed = relation"(x,y,z) where (x:n(1), y:n(2), z:n(3), w:n(4)) {
  R(x,w);
  S(y,w);
  T(z,w);}"

  d = RelationDiagram([Expr(:n, 1), Expr(:n, 2), Expr(:n, 3)])
  add_box!(d, [Expr(:n, 1),Expr(:n, 4)], name=:R)
  add_box!(d, [Expr(:n, 2),Expr(:n, 4)], name=:S)
  add_box!(d, [Expr(:n, 3),Expr(:n, 4)], name=:T)
  add_junctions!(d, [Expr(:n, 1),Expr(:n, 2),Expr(:n, 3),Expr(:n, 4)], variable=[:x,:y,:z,:w])
  set_junction!(d, [1,4,2,4,3,4])
  set_junction!(d, [1,2,3], outer=true)
  @test parsed == d

  # Mixed types
  #------

  parsed = relation"(x,y,z) where (x:n(1), y:2, z:C, w:nothing) {
  R(x,w);
  S(y,w);
  T(z,w);}"

  d = RelationDiagram([Expr(:n, 1), :2, :C])
  add_box!(d, [Expr(:n, 1),:nothing], name=:R)
  add_box!(d, [:2,:nothing], name=:S)
  add_box!(d, [:C,:nothing], name=:T)
  add_junctions!(d, [Expr(:n, 1),:2,:C,:nothing], variable=[:x,:y,:z,:w])
  set_junction!(d, [1,4,2,4,3,4])
  set_junction!(d, [1,2,3], outer=true)
  @test parsed == d





  # Special case: closed diagram.
  parsed = relation"() where (S:Pop, I:Pop, R:Pop, D:Pop) {
  infect(S,I,I,I)
  disease(I,R)
  disease(I,D);}"
  @test all(==(:Pop), subpart(parsed, :port_type))

  # Untyped, named ports
  #---------------------

  parsed = relation"(start=u, stop=w) where (u, v, w) {
  E(src=u, tgt=v);
  E(src=v, tgt=w);}"
  d = RelationDiagram(2, port_names=[:start, :stop])
  add_box!(d, 2, name=:E)
  add_box!(d, 2, name=:E)
  add_junctions!(d, 3, variable=[:u,:v,:w])
  set_junction!(d, [1,2,2,3])
  set_junction!(d, [1,3], outer=true)
  set_subpart!(d, :port_name, [:src, :tgt, :src, :tgt])
  @test parsed == d

  # Context is inferred.
  d1 = relation"(start=u, mid=v, stop=w) where () {E(src=u, tgt=v); E(src=v, tgt=w);}"  
  d2 = relation"(start=u, mid=v, stop=w) where (u,v,w) {E(src=u, tgt=v); E(src=v, tgt=w);}"
  @test d1 == d2

  d1 = relation"(start=u, stop=w) where () {E(src=u, tgt=v); E(src=v, tgt=w);}"
  d2 = relation"(start=u, stop=w) where (u,w,v) {E(src=u, tgt=v); E(src=v, tgt=w);}"
  @test d1 == d2

  # Special case: unary named tuple syntax.
  parsed = relation"(src=v) where (v, w) {E(src=v, tgt=w);}"
  @test parsed[:outer_port_name] == [:src]

  # Special case: closed diagram.
  d1 = relation"() where (v) {E(src=v, tgt=v);}"
  @test subpart(d1, :port_name) == [:src, :tgt]

  d2 = relation"() where () {E(src=v, tgt=v);}"
  @test d1 == d2

  # Typed, named ports
  #-------------------

  parsed = relation"(e=e, e′=e′) where (e:Employee, e′:Employee, d:Department) {
  Employee(id=e, department=d);
  Employee(id=e′, department=d);}"

  d = RelationDiagram([:Employee, :Employee], port_names=[:e,:e′])
  add_box!(d, [:Employee, :Department], name=:Employee)
  add_box!(d, [:Employee, :Department], name=:Employee)
  add_junctions!(d, [:Employee, :Employee, :Department], variable=[:e,:e′,:d])
  set_junction!(d, [1,3,2,3])
  set_junction!(d, [1,2], outer=true)
  set_subpart!(d, :port_name, [:id, :department, :id, :department])
  @test parsed == d
end

# @testset "End-End Erroring" begin
#   # Test error handling
  
#   parsed_result = relation"""
#   (x, z) where (x:X, y:Y, z:Z)
#   {
#     R(x, y);
#     S(y, z);
#     T(z, y, u);
#   }"""

#   v1 = Typed(:x, :X)
#   v2 = Typed(:y, :Y)
#   v3 = Typed(:z, :Z)
#   v4 = Untyped(:u)
#   op = [v1, v3]
#   c = [v1, v2, v3]
#   s = [Statement(:R, [v1,v2]),
#     Statement(:S, [v2,v3]),
#     Statement(:T, [v3,v2, v4])]
#   u = UWDExpr(op, c, s)
#   uwd_result = RelationTerm.construct(RelationDiagram, u)

#   @test parsed_result == uwd_result
# end

end