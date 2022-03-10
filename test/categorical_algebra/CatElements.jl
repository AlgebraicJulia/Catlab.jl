module TestCatElements
using Test
using Catlab, Catlab.Theories, Catlab.Graphs, Catlab.CategoricalAlgebra

arr = @acset Graph begin
  V = 2
  E = 1
  src=[1]
  tgt=[2]
end
elarr = elements(arr)

@testset "Arrow Elements" begin
  @test nparts(elarr, :El)  == 3
  @test nparts(elarr, :Arr) == 2
  @test nparts(elarr, :Ob)  == 2
  @test nparts(elarr, :Hom) == 2
  @test elarr[:, :πₑ]    == [1,1,2]
  @test elarr[:, :πₐ]    == [1,2]
  @test elarr[:, :src]   == [3,3]
  @test elarr[:, :tgt]   == [1,2]
  @test elarr[:, :nameo] == [:V, :E]
  @test elarr[:, :nameh] == [:src, :tgt]
  @test elarr[:, :dom]   == [2, 2]
  @test elarr[:, :cod]   == [1, 1]
  @test inverse_elements(elarr, Graph()) == arr
end

b = @acset Graph begin
  V = 2
  E = 1
  src = [1]
  tgt = [2]
end
elb = elements(b)
ThBPG, obmap, hommap = CatElements.presentation(elb)
@test Symbol.(generators(ThBPG)) == [:V_1, :V_2, :E_1, :src_E_1, :tgt_E_1]
@test inverse_elements(elb, Graph()) == b

p₀ = @acset Graph begin
  V = 2
  E = 2
  src=[1,2]
  tgt=[2,1]
end
elpₒ = elements(p₀)
ThPetri, obmap, hommap = CatElements.presentation(elpₒ)
@test Symbol.(generators(ThPetri)) ==
  [:V_1, :V_2, :E_1, :E_2, :src_E_1, :src_E_2, :tgt_E_1, :tgt_E_2]

# Shuffle element-specific indices around, but leave fundamental data unchanged
elpₒ2 = @acset Elements{Symbol} begin
  El=4; Arr=4; Ob=2; Hom=2
  πₑ = [2,1,2,1] # we've swapped indices 2/3 and V/E and src/tgt
  src = [2,4,2,4]; tgt = [1,3,3,1]; πₐ=[2,2,1,1]
  nameo = [:E, :V]
  dom = [1,1]; cod=[2,2]; nameh = [:tgt, :src]
end

@test inverse_elements(elpₒ2, Graph()) == p₀ #
elpₒ3 = deepcopy(elpₒ)  # swap the two arrows in the category of elements
set_subpart!(elpₒ3, :src, [4,3,4,3]) # instead of 3,4,3,4
@test inverse_elements(elpₒ3, Graph()) != p₀
@test is_isomorphic(inverse_elements(elpₒ3, Graph()), p₀)

@acset_type Petri(ThPetri)

sir_eltsch = @acset Petri begin
  V_1 = 3
  V_2 = 2
  E_1 = 3
  E_2 = 3

  src_E_1 = [1,2,2]
  tgt_E_1 = [1,1,2]

  src_E_2 = [1,1,2]
  tgt_E_2 = [2,2,3]
end

@testset "DiBipartite Elements" begin
  @test length(generators(ThPetri)) == 8
  @test nparts(sir_eltsch, :V_1) == 3
  @test nparts(sir_eltsch, :V_2) == 2
  @test nparts(sir_eltsch, :E_1) == 3
  @test nparts(sir_eltsch, :E_2) == 3
  @test sir_eltsch[:, :src_E_2] == [1,1,2]
  @test inverse_elements(elements(sir_eltsch), sir_eltsch) == sir_eltsch
end

# Assign two tgt's to an edge
bad = @acset Elements{Symbol} begin
  El=2; Arr=3; Ob=2; Hom=2
  πₑ = [1,2]
  src = [2,2,1]; tgt = [1,1,1]; πₐ=[1,2,2]
  nameo = [:V, :E]
  dom = [2,2]; cod=[1,1]; nameh = [:src, :tgt]
end
@test_throws ErrorException inverse_elements(bad, Graph())

# Morphisms
###########
e1 = @acset Graph begin V=1;E=2; src=[1,1]; tgt=[1,1] end
swap = ACSetTransformation(e1,e1; V=[1],E=[2,1])
eswap = elements(swap)

@testset "Elements of graph homomorphism" begin
  @test collect(eswap[:El]) == [1,3,2]
  @test collect(eswap[:Arr]) == [2,1,4,3]
end
@testset "inverse of elements of homomorphism" begin
  @test inverse_elements(eswap, e1) == swap
  for h in homomorphisms(sir_eltsch, sir_eltsch) # 24
    @test inverse_elements(elements(h), sir_eltsch) == h
  end
end
end # module
