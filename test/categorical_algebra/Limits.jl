""" Tests of limit and colimit data structures.

More extensive tests are provided by (co)limits for specific categories such as
FinSet.
"""
module TestLimits
using Test

using StaticArrays
using Catlab.Theories
using Catlab.CategoricalAlgebra.FreeDiagrams, Catlab.CategoricalAlgebra.Limits

A, B, C = Ob(FreeCategory, :A, :B, :C)

# Limits
########

# Products.
f, g = Hom(:f, C, A), Hom(:g, C, B)
lim = Limit(SVector(A,B), Span(f,g))
@test lim isa BinaryProduct
@test ob(lim) == C
@test apex(lim) == C
@test legs(lim) == [f,g]

lim = Limit([A,B], Span(f,g))
@test lim isa Product

# Colimits
##########

# Coproducts.
f, g = Hom(:f, A, C), Hom(:g, B, C)
colim = Colimit(SVector(A,B), Cospan(f,g))
@test colim isa BinaryCoproduct
@test ob(colim) == C
@test base(colim) == C
@test legs(colim) == [f,g]

colim = Colimit([A,B], Cospan(f,g))
@test colim isa Coproduct

end
