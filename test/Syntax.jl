using Base.Test

using CompCat.GAT
using CompCat.Syntax

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

# @syntax FreeMonoidAssoc Monoid begin
#   mtimes(x::M, y::M) = Super.mtimes(x,y)
# end
