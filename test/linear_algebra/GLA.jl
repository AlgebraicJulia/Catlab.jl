module TestGraphicalLinearAlgebra
using Test

using Catlab.LinearAlgebra

# Doctrines
###########

# Linear maps
#------------

A, B = Ob(FreeLinearMaps, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, A, B)

# Domains and codomains
@test dom(plus(f,g)) == A
@test codom(plus(f,g)) == B

# Unicode syntax
@test f+g == plus(f,g)

end
