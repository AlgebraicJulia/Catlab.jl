
# Pushout with names.
A, B = FinSet([:w, :x, :y1]), FinSet([:x, :y2, :z])
f, g = FinFunction(Dict(:y => :y1), A), FinFunction(Dict(:y => :y2), B)
colim = pushout(f, g)
C = ob(colim)
@test Set(C) == Set([:w, Symbol("x#1"), Symbol("x#2"), :y, :z])
ι1, ι2 = colim
@test ι1 == FinFunction(Dict(:w => :w, :x => Symbol("x#1"), :y1 => :y), C)
@test ι2 == FinFunction(Dict(:x => Symbol("x#2"), :y2 => :y, :z => :z), C)
