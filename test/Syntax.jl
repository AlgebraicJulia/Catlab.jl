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
@test isa(munit(FreeMonoid.M), FreeMonoid.M)

# @syntax FreeMonoidAssoc Monoid begin
#   mtimes(x::M, y::M) = Super.mtimes(x,y)
# end
