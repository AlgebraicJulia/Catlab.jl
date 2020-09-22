""" Tests of limit and colimit data structures.

More extensive tests are provided by (co)limits for specific categories such as
FinSet.
"""
module TestLimits
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra

A, B, C = Ob(FreeCategory, :A, :B, :C)

# Limits
########

# Products.
f, g = Hom(:f, C, A), Hom(:g, C, B)
lim = Limit(ObjectPair(A,B), Span(f,g))
@test lim isa BinaryProduct
@test ob(lim) == C
@test apex(lim) == C
@test legs(lim) == [f,g]

lim = Limit(DiscreteDiagram([A,B]), Span(f,g))
@test lim isa Product

# Colimits
##########

# Coproducts.
f, g = Hom(:f, A, C), Hom(:g, B, C)
colim = Colimit(ObjectPair(A,B), Cospan(f,g))
@test colim isa BinaryCoproduct
@test ob(colim) == C
@test apex(colim) == C
@test legs(colim) == [f,g]

colim = Colimit(DiscreteDiagram([A,B]), Cospan(f,g))
@test colim isa Coproduct

end
