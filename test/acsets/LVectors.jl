module TestLVectors
using Test

using Catlab.LVectors

x = LVector{(:a,:b,:c)}([3,5,7])
@test eltype(x) == Int
@test size(x) == (3,)
@test length(x) == 3

# Equality and hashing.
@test x == copy(x)
@test hash(x) == hash(copy(x))
x′ = LVector{(:x,:y,:z)}([3,5,7])
@test x != x′
@test hash(x) != hash(x′)

# Getters.
@test x[2] == 5
@test x[:a] == 3

# Setters.
x[1] = 4
@test x[1] == 4
x[:b] = 6
@test x[:b] == 6

end # module