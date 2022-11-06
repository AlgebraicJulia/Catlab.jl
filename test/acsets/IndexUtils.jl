module TestIndexUtils

using Test
using Catlab.IndexUtils 

x = [1,3,5]
insertsorted!(x, 2)
@test x == [1,2,3,5]

deletesorted!(x, 3)
@test x == [1,2,5]

ss = SortedSet{Int}()
push!(ss, 2)
push!(ss, 1)
@test collect(ss) == values(ss) == [1,2]
@test length(ss) == 2
delete!(ss, 1)
@test length(ss) == 1
@test 1 ∉ ss
ss2 = copy(ss)
push!(ss2, 3)
@test length.([ss,ss2]) == [1,2]

end # module
