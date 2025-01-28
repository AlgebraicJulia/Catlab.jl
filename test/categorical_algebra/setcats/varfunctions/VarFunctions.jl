module TestVarFunctions

using Catlab, Test

# THIS IS A BAD CATEGORY (COPROD OF ALL T's)
# const Sk = SkelKleisliT()
# f = FinDomFunction([Left(1), Right.([1,2,3])...], either(FinSet(1), SetOb(Int)))
# @test dom[Sk](f) == FinSet(4)
# @test codom[Sk](f) == FinSet(1)

# @test f(1) == Left(1)
# @test f(2) == Right(1)

# # Composition 
# #------------
# force_compose(x,y) = force(compose[Sk](x,y))
# boolT(x) = either(x, SetOb(Bool))
# f = FinDomFunction(([Left(2), Left(1), Right(true)]), boolT(FinSet(3)))
# g = FinDomFunction(Left.([2,3,4]), boolT(FinSet(4)))

# @test codom[Sk](f) == dom[Sk](g)
# @test force_compose(f, g) |> collect == [Left(3),Left(2), Right(true)]

# @test collect(force_compose(id[Sk](FinSetInt(3)), f)) == [Left(2), Left(1), Right(true)]


# compose[Sk](f,id[Sk](FinSetInt(3)))


end # module