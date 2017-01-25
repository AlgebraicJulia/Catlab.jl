using CompCat.Syntax
using Base.Test

f = mor(:f, ob(:A), ob(:A))
g = mor(:g, ob(:A), ob(:A))
@test compose(compose(f,g),f) == compose(f,compose(g,f))
