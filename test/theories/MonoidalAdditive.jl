using Test

# Symmetric monoidal category
#############################

A, B = Ob(FreeSymmetricMonoidalCategoryAdditive, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Domains and codomains
@test dom(oplus(f,g)) == oplus(dom(f),dom(g))
@test codom(oplus(f,g)) == oplus(codom(f),codom(g))
@test dom(swap(A,B)) == oplus(A,B)
@test codom(swap(A,B)) == oplus(B,A)

# Associativity and unit
O = mzero(FreeSymmetricMonoidalCategoryAdditive.Ob)
@test oplus(A,O) == A
@test oplus(O,A) == A
@test oplus(oplus(A,B),A) == oplus(A,oplus(B,A))
@test oplus(oplus(f,g),f) == oplus(f,oplus(g,f))

# Extra syntax
@test oplus(A,B,A) == oplus(oplus(A,B),A)
@test oplus([A,B,A]) == oplus(oplus(A,B),A)
@test oplus(f,f,f) == oplus(oplus(f,f),f)
@test oplus([f,f,f]) == oplus(oplus(f,f),f)
@test oplus(FreeSymmetricMonoidalCategoryAdditive.Ob[]) == O
@test_throws MethodError oplus([])
@test A⊕B == oplus(A,B)
@test f⊕g == oplus(f,g)
@test A⊕B⊕A == oplus(A,B,A)

# Extra functions
@test collect(A) == [A]
@test collect(oplus(A,B)) == [A,B]
@test collect(O) == []
@test typeof(collect(O)) == Vector{FreeSymmetricMonoidalCategoryAdditive.Ob}
@test ndims(A) == 1
@test ndims(oplus(A,B)) == 2
@test ndims(O) == 0

# String format
@test string(oplus(f,g)) == "oplus(f,g)"
@test string(compose(oplus(f,f),oplus(g,g))) == "compose(oplus(f,f),oplus(g,g))"

# S-expressions
@test sexpr(O) == "(mzero)"
@test sexpr(oplus(A,B)) == "(oplus :A :B)"
@test sexpr(oplus(f,g)) == "(oplus :f :g)"
@test sexpr(compose(oplus(f,f),oplus(g,g))) == "(compose (oplus :f :f) (oplus :g :g))"

# Infix notation (Unicode)
@test unicode(O) == "O"
@test unicode(oplus(A,B)) == "A⊕B"
@test unicode(oplus(f,g)) == "f⊕g"
@test unicode(compose(oplus(f,f),oplus(g,g))) == "(f⊕f)⋅(g⊕g)"
@test unicode(oplus(compose(f,g),compose(g,f))) == "(f⋅g)⊕(g⋅f)"

# Infix notation (LaTeX)
@test latex(O) == "O"
@test latex(oplus(A,B)) == "A \\oplus B"
@test latex(oplus(f,g)) == "f \\oplus g"
@test latex(compose(oplus(f,f),oplus(g,g))) == 
  "\\left(f \\oplus f\\right) \\cdot \\left(g \\oplus g\\right)"
@test latex(oplus(compose(f,g),compose(g,f))) == 
  "\\left(f \\cdot g\\right) \\oplus \\left(g \\cdot f\\right)"
@test latex(swap(A,B)) == "\\sigma_{A,B}"

# Cocartesian category
######################

A, B = Ob(FreeCocartesianCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

# Domains and codomains
@test dom(plus(A)) == oplus(A,A)
@test codom(plus(A)) == A
@test dom(zero(A)) == O
@test codom(zero(A)) == A

# Derived syntax
@test copair(f,f) == compose(oplus(f,f), plus(B))
@test coproj1(A,B) == oplus(id(A), zero(B))
@test coproj2(A,B) == oplus(zero(A), id(B))

# LaTeX notation
@test latex(plus(A)) == "\\nabla_{A}"
@test latex(zero(A)) == "0_{A}"
