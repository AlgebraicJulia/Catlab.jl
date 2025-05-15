module TestCategories

using Test, Catlab, GATlab

# Categories
############
M = TypeCat(FreeCategory.Meta.M);
C = Category(M)
@test getvalue(C) isa TypeCat{FreeCategory.Ob, FreeCategory.Hom}
@test C isa Category

x, y = Ob(FreeCategory, :x, :y)
f = Hom(:f, x, y)

Co = op(C)
@test codom(C, f) == dom(Co, f) == codom(f) == y


# Coproduct Categories
#######################
C2 = Category(DiscreteFinCat(FinSet(2)))
cats = Category.([TrivialCat(), C2])
cp = CoproductCat(cats) |> Category

n1 = TaggedElem(nothing, 1)
two2 = TaggedElem(2, 2)
@test n1 == id(cp, n1)
@test two2 == id(cp, two2)
@test two2 == compose(cp, two2, two2)

end # module
