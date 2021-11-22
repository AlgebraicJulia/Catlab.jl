""" Tests of limits and colimits in general.

More extensive tests are provided by tests of (co)limits in specific categories
such as Set and FinSet.
"""
module TestLimits
using Test

using Catlab.Theories, Catlab.CategoricalAlgebra

A, B, C = Ob(FreeCategory, :A, :B, :C)

# Limits
########

# Limit data structure.
f, g = Hom(:f, C, A), Hom(:g, C, B)
lim = Limit(ObjectPair(A,B), Span(f,g))
@test lim isa BinaryProduct
@test ob(lim) == C
@test apex(lim) == C
@test legs(lim) == [f,g]

lim = Limit(DiscreteDiagram([A,B]), Span(f,g))
@test lim isa Product

# Specializing to singleton limit.
d = FreeDiagram{FreeCategory.Ob,FreeCategory.Hom}(1, ob=A)
lim = limit(d, SpecializeLimit())
@test ob(lim) == A

# Colimits
##########

# Colimit data structure.
f, g = Hom(:f, A, C), Hom(:g, B, C)
colim = Colimit(ObjectPair(A,B), Cospan(f,g))
@test colim isa BinaryCoproduct
@test ob(colim) == C
@test apex(colim) == C
@test legs(colim) == [f,g]

colim = Colimit(DiscreteDiagram([A,B]), Cospan(f,g))
@test colim isa Coproduct

# Specializing to singleton colimit.
d = FreeDiagram{FreeCategory.Ob,FreeCategory.Hom}(1, ob=A)
colim = colimit(d, SpecializeColimit())
@test ob(colim) == A

end
