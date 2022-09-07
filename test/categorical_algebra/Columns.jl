module TestColumns

using Test
using Catlab.Columns

# Mappings
##########

m = PartialVecMap{Int}()

@test_throws BoundsError m[1]
@test_throws BoundsError (m[1] = 2)

dom_hint!(m, Base.OneTo(5))

@test_throws AssertionError m[1]

m[1] = 2

@test m[1] == 2
@test defined_indices(m) == [1]
@test defined_values(m) == [2]

undefine!(m, 1)

@test_throws AssertionError m[1]
@test defined_indices(m) == []
@test defined_values(m) == []

m = DefaultVecMap{Int,DefaultVal{Int,0}}()

@test_throws BoundsError m[1]
@test_throws BoundsError (m[1] = 2)

dom_hint!(m, Base.OneTo(5))

@test m[1] == 0

m[1] = 2

@test m[1] == 2
@test defined_indices(m) == 1:5
@test defined_values(m) == [2,0,0,0,0]

undefine!(m, 1)

@test m[1] == 0
@test defined_indices(m) == 1:5
@test defined_values(m) == [0,0,0,0,0]

m = PartialDictMap{Symbol, Int}()

@test_throws KeyError m[:a]

m[:a] = 2

@test m[:a] == 2

@test [defined_indices(m)...] == [:a]
@test [defined_values(m)...] == [2]

undefine!(m, :a)

@test Symbol[defined_indices(m)...] == Symbol[]
@test Int[defined_values(m)...] == Int[]

m = DefaultDictMap{Symbol, Vector{Int}, DefaultEmpty{Vector{Int}}}()

@test m[:a] == []

m[:a] = [2,3,4]

@test m[:a] == [2,3,4]

@test [defined_indices(m)...] == [:a]
@test [defined_values(m)...] == [[2,3,4]]

# InvMappings
#############

m = PartialVecMap{Symbol}(4)
i = TrivialIM{Int,Symbol}()

m[1] = :a
m[2] = :b
m[3] = :b
m[4] = :c

@test inverse(m, i, :b) == [2,3]

undefine!(m, 3)

@test inverse(m, i, :b) == [2]
@test inverse(m, i, :c) == [4]

i = StoredPreimageIM(DefaultDictMap{Symbol, Set{Int}, DefaultEmpty{Set{Int}}}())
add_mapping!(i, :a, 1)
add_mapping!(i, :b, 2)
add_mapping!(i, :c, 4)

@test [inverse(m, i, :b)...] == [2]

remove_mapping!(i, :c, 4)

@test [inverse(m, i, :c)...] == []

# Columns
#########

m = column_type(Hom(NoIndex))()
m = column_type(Hom(Index))()
m = column_type(Hom(UniqueIndex))()

m = column_type(Attr(NoIndex, String))()
m = column_type(Attr(Index, String))()
m = column_type(Attr(UniqueIndex, String))()

m = column_type(Attr(NoIndex, nothing)){String}()
m = column_type(Attr(Index, nothing)){String}()
m = column_type(Attr(UniqueIndex, nothing)){String}()

end
