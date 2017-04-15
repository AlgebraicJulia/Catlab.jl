""" Test the Syntax module.

The unit tests are sparse because many of the Doctrine tests are really just
tests of the Syntax module.
"""
module TestSyntax

using Base.Test
using CompCat.GAT
using CompCat.Syntax

# Simple case: Monoid (no dependent types)

""" Signature of the theory of monoids.
"""
@signature Monoid(M) begin
  M::TYPE
  munit()::M
  mtimes(x::M,y::M)::M
end

""" Syntax for the theory of monoids.
"""
@syntax FreeMonoid Monoid

@test isa(FreeMonoid, Module)
@test contains(string(Docs.doc(FreeMonoid)), "theory of monoids")
@test sort(names(FreeMonoid)) == sort([:FreeMonoid, :M])

x, y, z = FreeMonoid.m(:x), FreeMonoid.m(:y), FreeMonoid.m(:z)
@test x == FreeMonoid.m(:x)
@test x != y
@test FreeMonoid.m("X") == FreeMonoid.m("X")
@test FreeMonoid.m("X") != FreeMonoid.m("Y")

@test isa(mtimes(x,y), FreeMonoid.M)
@test isa(munit(FreeMonoid.M), FreeMonoid.M)
@test mtimes(mtimes(x,y),z) != mtimes(x,mtimes(y,z))

@syntax FreeMonoidAssoc Monoid begin
  mtimes(x::M, y::M) = associate(Super.mtimes(x,y))
end

x, y, z = FreeMonoidAssoc.m(:x), FreeMonoidAssoc.m(:y), FreeMonoidAssoc.m(:z)
e = munit(FreeMonoidAssoc.M)
@test mtimes(mtimes(x,y),z) == mtimes(x,mtimes(y,z))
@test mtimes(e,x) != x && mtimes(x,e) != x

@syntax FreeMonoidAssocUnit Monoid begin
  mtimes(x::M, y::M) = associate_unit(Super.mtimes(x,y), munit)
end

x, y, z = FreeMonoidAssocUnit.m(:x), FreeMonoidAssocUnit.m(:y), FreeMonoidAssocUnit.m(:z)
e = munit(FreeMonoidAssocUnit.M)
@test mtimes(mtimes(x,y),z) == mtimes(x,mtimes(y,z))
@test mtimes(e,x) == x && mtimes(x,e) == x

abstract MonoidExpr{T} <: BaseExpr{T}
@syntax FreeMonoidTyped(MonoidExpr) Monoid

x = FreeMonoidTyped.m(:x)
@test issubtype(FreeMonoidTyped.M, MonoidExpr)
@test isa(x, FreeMonoidTyped.M) && isa(x, MonoidExpr)

# Category (includes dependent types)

@signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  
  id(X::Ob)::Hom(X,X)
  compose(f::Hom(X,Y), g::Hom(Y,Z))::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob)
  
  compose(fs::Vararg{Hom}) = foldl(compose, fs)
end

@syntax FreeCategory Category begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g))
end

@test isa(FreeCategory, Module)
@test sort(names(FreeCategory)) == sort([:FreeCategory, :Ob, :Hom])

X, Y, Z, W = map(FreeCategory.ob, [:X, :Y, :Z, :W])
f = FreeCategory.hom(:f, X, Y)
g = FreeCategory.hom(:g, Y, Z)
h = FreeCategory.hom(:h, Z, W)
@test isa(X, FreeCategory.Ob) && isa(f, FreeCategory.Hom)
@test_throws MethodError FreeCategory.hom(:f)
@test dom(f) == X
@test codom(f) == Y

@test isa(id(X), FreeCategory.Hom)
@test dom(id(X)) == X
@test codom(id(X)) == X

@test isa(compose(f,g), FreeCategory.Hom)
@test dom(compose(f,g)) == X
@test codom(compose(f,g)) == Z
@test isa(compose(f,f), FreeCategory.Hom) # Doesn't check domains.

@test compose(compose(f,g),h) == compose(f,compose(g,h))
@test compose(f,g,h) == compose(compose(f,g),h)
@test dom(compose(f,g,h)) == X
@test codom(compose(f,g,h)) == W

@syntax FreeCategoryStrict Category begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

X, Y = FreeCategoryStrict.ob(:X), FreeCategoryStrict.ob(:Y)
f = FreeCategoryStrict.hom(:f, X, Y)
g = FreeCategoryStrict.hom(:g, Y, X)

@test isa(compose(f,g,f), FreeCategoryStrict.Hom)
@test_throws SyntaxDomainError compose(f,f)

@signature Monoid(M) => MonoidNumeric(M) begin
  elem_int(x::Int)::M
end
@syntax FreeMonoidNumeric MonoidNumeric

x = elem_int(FreeMonoidNumeric.M, 1)
@test isa(x, FreeMonoidNumeric.M)

end
