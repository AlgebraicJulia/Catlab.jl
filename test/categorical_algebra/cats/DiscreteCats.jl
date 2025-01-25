module TestDiscreteCats 

using Catlab, Test

sshow(args...) = sprint(show, args...)

# Discrete categories.
C = FinCat(FinSet(3))
@test C isa FinCat{Int,Int}
@test is_discrete(C)
@test collect(ob_generators(C)) == 1:3
@test isempty(hom_generators(C))
@test (dom(C, 1), codom(C, 1)) == (1, 1)
@test (id(C, 2), compose(C, 2, 2)) == (2, 2)
@test sshow(C) == "FinCat(3)"

F = FinDomFunctor([FinSet(1), FinSet(3), FinSet(1)],
                  C, TypeCat(FinSet{Int}, FinFunction{Int}))
@test ob_map(F, 2) == FinSet(3)
@test hom_map(F, 2) == id(FinSet(3))

end # module
