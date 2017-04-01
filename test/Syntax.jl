""" Test the Syntax module.

The unit tests are sparse because many of the Doctrine tests are really just
tests of the Syntax module.
"""
module TestSyntax

using Base.Test

using CompCat.GAT
using CompCat.Syntax

# Simple case: Monoid (no dependent types)

@signature Monoid(M) begin
  M::TYPE
  munit()::M
  mtimes(x::M,y::M)::M
end

@syntax FreeMonoid Monoid
@test isa(FreeMonoid, Module)
@test sort(names(FreeMonoid)) == sort([:FreeMonoid, :M])

x, y, z = FreeMonoid.m(:x), FreeMonoid.m(:y), FreeMonoid.m(:z)
@test x == FreeMonoid.m(:x)
@test x != y
@test isa(mtimes(x,y), FreeMonoid.M)
@test isa(munit(FreeMonoid.M), FreeMonoid.M)
@test mtimes(mtimes(x,y),z) != mtimes(x,mtimes(y,z))

@syntax FreeMonoidAssoc Monoid begin
  mtimes(x::M, y::M) = associate(FreeMonoidAssoc.mtimes(x,y))
end

x, y, z = FreeMonoidAssoc.m(:x), FreeMonoidAssoc.m(:y), FreeMonoidAssoc.m(:z)
e = munit(FreeMonoidAssoc.M)
@test mtimes(mtimes(x,y),z) == mtimes(x,mtimes(y,z))
@test mtimes(e,x) != x && mtimes(x,e) != x

@syntax FreeMonoidAssocUnit Monoid begin
  mtimes(x::M, y::M) = associate(:munit, FreeMonoidAssocUnit.mtimes(x,y))
end

x, y, z = FreeMonoidAssocUnit.m(:x), FreeMonoidAssocUnit.m(:y), FreeMonoidAssocUnit.m(:z)
e = munit(FreeMonoidAssocUnit.M)
@test mtimes(mtimes(x,y),z) == mtimes(x,mtimes(y,z))
@test mtimes(e,x) == x && mtimes(x,e) == x

# Category (includes dependent types)

@signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  
  id(X::Ob)::Hom(X,X)
  compose(f::Hom(X,Y),g::Hom(Y,Z))::Hom(X,Z) <= (X::Ob, Y::Ob, Z::Ob)
  
  compose(fs::Vararg{Hom}) = foldl(compose, fs)
end

@syntax FreeCategory Category
@test isa(FreeCategory, Module)
@test sort(names(FreeCategory)) == sort([:FreeCategory, :Ob, :Hom])

X, Y, Z = FreeCategory.ob(:X), FreeCategory.ob(:Y), FreeCategory.ob(:Z)
f, g = FreeCategory.hom(:f, X, Y), FreeCategory.hom(:f, Y, Z)
@test isa(X, FreeCategory.Ob) && isa(f, FreeCategory.Hom)
@test_throws MethodError FreeCategory.hom(:f)
#@test dom(f) == X && codom(f) == Y

@test isa(id(X), FreeCategory.Hom)
#@test dom(id(X)) == X && codom(id(X)) == X
@test isa(compose(f,g), FreeCategory.Hom)

end
