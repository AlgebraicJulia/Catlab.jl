module TestCategories

using Test, Catlab, GATlab

# Instances
###########

# Categories
#-----------
M = TypeCat(FreeCategory.Meta.M);
C = Category(M)
@test getvalue(C) isa TypeCat{FreeCategory.Ob, FreeCategory.Hom}
@test C isa Category

x, y = Ob(FreeCategory, :x, :y)
f = Hom(:f, x, y)

Co = op(C)
@test codom(C, f) == dom(Co, f) == codom(f) == y

end # module
