module TestSetCLimits 

using Test, Catlab

const 𝒞 = SetC()

# Binary product.
#-----------------
DD = DiscreteDiagram([SetOb(Int), SetOb(String)])
lim = limit[𝒞](DD)
@test ob(lim) == SetOb(ProdSet([SetOb(Int), SetOb(String)]))
π1, π2 = lim
@test (π1((1,"foo")), π2((1,"foo"))) == (1,"foo")

f = SetFunction(length, SetOb(Vector{String}), SetOb(Int))
g = SetFunction(v -> sprint(join, v), SetOb(Vector{String}), SetOb(String))
@test pair[𝒞](lim, f, g)(["foo", "bar", "baz"]) == (3, "foobarbaz")



# N-ary product.
#----------------
lim = product[𝒞](fill(SetOb(Int), 3)...)
@test eltype(ob(lim)) == (Tuple{Int,Int,Int})
π1, π2, π3 = lim
@test (π1((1,2,3)), π2((1,2,3)), π3((1,2,3))) == (1,2,3)

fs = [ SetFunction(x -> x+i, SetOb(Int), SetOb(Int)) for i in 1:3 ]
@test pair[𝒞](lim, fs)(3) == (4,5,6)

# Cartesian monoidal structure.
#------------------------------
CMC = TypedCatWithProducts(𝒞)
@withmodel CMC (⊗, munit, σ, proj1, proj2, Δ, ◊, id) begin
  @test eltype(SetOb(Int) ⊗ SetOb(String)) == Tuple{Int,String}
  @test munit() == SetOb(FinSet(nothing))
  @test σ(SetOb(Int), SetOb(String))((1,"foo")) == ("foo",1)
  π1 = proj1(SetOb(Int), SetOb(String))
  π2 = proj2(SetOb(Int), SetOb(String))
  @test (π1((1,"foo")), π2((1,"foo"))) == (1,"foo")
  @test (f⊗g)((["foo"], ["bar", "baz"])) == (1, "barbaz")
  @test Δ(SetOb(Int))(2) == (2,2)
  @test ◊(SetOb(Int))(1) == nothing
end

# TODO
# @test eltype(otimes(CMC, fill(SetOb(Int), 3)...)) == Tuple{Int,Int,Int}
# @test otimes(CMC, fs)((1,5,10)) == (2,7,13)

# no we can't actually take pullbacks in Set
if false 
# Pullback of a cospan into non-finite set.
f = FinDomFunction([:a, :a, :c, :b], SetOb(Symbol)) |> SetFunction
g = FinDomFunction([:a, :a, :d, :b], SetOb(Symbol)) |> SetFunction
π1, π2 = lim = pullback[𝒞](f, g)
@test ob(lim) == FinSet(5)
@test force(π1) == FinFunction([1,1,2,2,4], 4)
@test force(π2) == FinFunction([1,2,1,2,4], 4)

# Ternary pullback using different algorithms.
f, g = FinDomFunction.([[:a,:b,:c],[:c,:b,:a]], Ref(SetOb(Symbol)))
h = FinDomFunction([:a,:a,:b,:b,:c,:c], SetOb(Symbol))
fgh = Multicospan([f, g, h])
lim = limit[𝒞](fgh)
@test ob(lim) == FinSet(6)

tuples(lim::AbsLimit) =
  sort!([ Tuple(map(π -> π(i), legs(lim))) for i in ob(lim) ])

reference_tuples = tuples(lim)

# for alg in (NestedLoopJoin(), SortMergeJoin(), HashJoin())
#   lim = limit(fgh, C, alg)
#   @test ob(lim) == FinSet(6)
#   @test tuples(lim) == reference_tuples
# end


# Equalizer as limit of bipartite free diagram.
f, g = [FinDomFunction(x -> x % i, FinSet(100), SetOb(Int)) for i in 2:3]
d = BipartiteFreeDiagram(ParallelMorphisms([f, g]))
lim = (ι,) = limit[𝒞](d)
@test ι == incl(equalizer[𝒞](f, g))

# Two pullbacks, which should be reduced to a single pullback by pairing.
f1, f2 = FinDomFunction.([[1,1,2,2,3,3],[1,2,3]], Ref(SetOb(Int))) 
g1, g2 = FinDomFunction.([[:a,:a,:a,:b,:b,:b],[:a,:b,:c]], Ref(SetOb(Symbol)))
d = BipartiteFreeDiagram{SetOb,SetFunction}()
add_vertices₁!(d, 2; ob₁=[FinSet(6), FinSet(3)])
add_vertices₂!(d, 2; ob₂=[SetOb(Int), SetOb(Symbol)])
add_edges!(d, [1,1,2,2], [1,2,1,2], hom=[f1,g1,f2,g2])
lim = π1, π2 = limit[𝒞](d)
@test π1 == FinFunction([1,2,4], 6)
@test π2 == FinFunction([1,1,2], 3)
end # false 

end # module
