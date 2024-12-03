module TestParserCore

using Test

using Catlab.Parsers.ParserCore

@testset "Lexical Rules" begin
  @test ws("  ")[1] == "  "
  @test eq("=")[1] == "="
  @test lparen("(")[1] == "("
  @test rparen(")")[1] == ")"
  @test comma(",")[1] == ","
  @test EOL("\n")[1] == "\n"
  @test EOL(";")[1] == ";"
  @test colon(":")[1] == ":"
  @test ident("abc")[1] == "abc"
end

# Syntactic Rule Tests

@testset "Expression Parsing" begin
  @test expr("f()")[1] == Expr(:f)
  @test expr("f(a)")[1] == Expr(:f, :a)
  @test expr("f(a, b, c)")[1] == Expr(:f, :a, :b, :c)
end

end