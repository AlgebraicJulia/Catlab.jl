using Test

# Thin category
###############

x,y,z = Ob(FreeThinCategory, :x, :y, :z)
f, g = Hom(:f, x, y), Hom(:g, y, z)
@test dom(compose(f,g)) == x
@test codom(compose(f,g)) == z

x,y,z,zz = Ob(FreeThinSymmetricMonoidalCategory, :x, :y, :z, :zz)
f, g, h= Hom(:f, x, y), Hom(:g, y, z), Hom(:h, otimes(y,y), z)
j = Hom(:j, y⊗z, zz)
@test dom(compose(f,g)) == x
@test codom(compose(f,g)) == z
@test dom(otimes(f,g)) == otimes(x,y)
@test codom(otimes(f,g)) == otimes(y,z)
@test dom((f⊗id(y))⋅h) == x⊗y
@test codom((f⊗id(y))⋅h) == z
@test dom((f⊗g)⋅j) == x⊗y
@test codom((f⊗g)⋅j) == zz

# Preorder
##########

x,y,z = (Elt(FreePreorder.Elt, sym) for sym in (:x, :y, :z))
f, g = Leq(:f, x, y), Leq(:g, y, z)
@test lhs(reflexive(x)) == x
@test rhs(reflexive(x)) == x
@test lhs(transitive(f,g)) == x
@test rhs(transitive(f,g)) == z
