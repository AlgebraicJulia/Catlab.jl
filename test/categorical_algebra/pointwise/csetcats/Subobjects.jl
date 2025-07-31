module TestCSetSubobjects

using Catlab, Test

#########
# Graph #
#########

const Grph = ACSetCategory(CSetCat(Graph()))
const CM = TypedCatWithCoproducts(Grph)

# Construct sub-C-sets.
#----------------------
X = path_graph(Graph, 4)
A = Subobject(X, V=[2,3,4], E=[2,3])
@test ob(A) == X
α = hom(A)
@test is_natural(α)
@test dom(α) == path_graph(Graph, 3)
@test codom(α) == X
A_pred = Subobject(X, V=[false,true,true,true], E=[false,true,true])
@test hom(A_pred) == α

# Lattice of sub-C-sets.
#----------------------
X = @acset Graph begin V=6; E=5; src=[1,2,3,4,4]; tgt=[3,3,4,5,6] end
A, B = Subobject(X, V=1:4, E=1:3), Subobject(X, V=3:6, E=3:5)

@withmodel Grph (∧, ∨, ⊤, ⊥, bottom) begin 
  @test A ∧ B |> force == Subobject(X, V=3:4, E=3:3) |> force
  @test A ∨ B |> force == Subobject(X, V=1:6, E=1:5) |> force
  @test ⊤(X) |> force == Subobject(X, V=1:6, E=1:5) |> force
  @test ⊥(X) |> force == Subobject(X, V=1:0, E=1:0) |> force
  @test ⊥(X)  == bottom(X)
end 

# Bi-Heyting algebra of sub-C-sets.
###################################

# Implication in Graph (Reyes et al 2004, Sec 9.1, p. 139).
#-----------------------------------------------------------
I = Graph(1)
Y, Z = @withmodel CM (⊕) begin 
  Y = path_graph(Graph, 3) ⊕ path_graph(Graph, 2) ⊕ path_graph(Graph, 2)
  add_vertex!(Y)
  add_edge!(Y, 2, 8)
  Z = cycle_graph(Graph, 1) ⊕ cycle_graph(Graph, 1)
  Y, Z
end

ιY, ιZ = colim = pushout[Grph](ACSetTransformation(I, Y, V=[3]),
                               ACSetTransformation(I, Z, V=[1]))
B_implies_C, B = Subobject(ιY), Subobject(ιZ)
C = Subobject(ob(colim), V=2:5, E=2:3)
@withmodel Grph (⟹) begin 
  @test (B ⟹ C) |> force == B_implies_C |> force
end

# Subtraction in Graph (Reyes et al 2004, Sec 9.1, p. 144).
#-----------------------------------------------------------
X = ob(colim)
C = Subobject(X, V=2:5, E=[2,3,ne(X)-1])
@withmodel Grph (\) begin 
@test (B \ C) |> force == Subobject(X, V=[nv(X)], E=[ne(X)]) |> force
end 

# Negation in Graph (Reyes et al 2004, Sec 9.1, p. 139-140).
#-----------------------------------------------------------

X = @withmodel CM (⊕) begin 
 cycle_graph(Graph, 1) ⊕ path_graph(Graph, 2) ⊕ cycle_graph(Graph, 4)
end
add_vertex!(X)
add_edge!(X, 4, 8)
A = Subobject(X, V=[2,3,4,5,8], E=[3,7])
neg_A = Subobject(X, V=[1,6,7], E=[1,5])
@test is_natural(hom(A)) && is_natural(hom(neg_A))

@withmodel Grph (¬) begin 
  @test ¬A |> force == neg_A |> force
  @test ¬neg_A |> force == Subobject(X, V=[2,3,4,5,8], E=[2,3,7]) |> force
end 

# Non in Graph (Reyes et al 2004, Sec 9.1, p. 144).
#-------------------------------------------------

X = @withmodel CM (⊕) begin 
 path_graph(Graph, 5) ⊕ path_graph(Graph, 2) ⊕ cycle_graph(Graph, 1)
end
A = Subobject(X, V=[1,4,5], E=[4])
non_A = Subobject(X, V=setdiff(vertices(X), 5), E=setdiff(edges(X), 4))
@withmodel Grph (~) begin 
  @test ~A |> force == non_A |> force
  @test ~non_A |> force == Subobject(X, V=[4,5], E=[4]) |> force
end


# Image and preimage
####################

g1 = path_graph(Graph, 2)
g2 = apex(coproduct[Grph](g1, g1))
g3 = @acset Graph begin V=2; E=3; src=[1,1,2]; tgt=[1,2,2] end
h = homomorphisms(g1,g2)[2] # V=[3,4], E=[2]
ϕ = homomorphism(g2,g3; initial=(V=[1,1,2,2],))

@test components(hom(h(g1))) == (
  V = FinFunction([3, 4], 2, 4), E = FinFunction([2], 1, 2))
@test preimage(h, g2) |> force == (top[Grph](g1) |> force)
@test preimage(h, Subobject(g2, V=[1])) |> force == bottom[Grph](g1) |> force
@test preimage(h, Subobject(g2, V=[3])) |> force == Subobject(g1, V=[1]) |> force
@test ϕ(h(g1)) == Subobject(g3, V=[2], E=[3])

# Preimage
#---------
G = @withmodel CM (⊕) begin 
  path_graph(Graph, 1) ⊕ path_graph(Graph, 2) ⊕ path_graph(Graph, 3)
end
H = let Loop=apex(terminal[Grph]()); 
  @withmodel CM (⊕) begin 
    Loop ⊕ Loop ⊕ Loop 
  end
end

# Each path graph gets its own loop
f = homomorphism(G, H; initial=(V=Dict([1=>1,2=>2,4=>3]),))
for i in 1:3
  @test is_isomorphic(dom(hom(preimage(f, Subobject(H, V=[i],E=[i])))),
                      path_graph(Graph, i))
end

############################
# Negation and non in DDS. #
############################

@present SchDDS(FreeSchema) begin X::Ob; Φ::Hom(X,X) end
@acset_type DDS(SchDDS, index=[:Φ])
const 𝒞 = ACSetCategory(CSetCat(DDS()))


S₁ = DDS(); add_parts!(S₁, :X, 5, Φ=[3,3,4,5,5])
S₂ = DDS(); add_parts!(S₂, :X, 3, Φ=[2,3,3])
ι₁, ι₂ = colim = coproduct[𝒞](S₁, S₂)
S = ob(colim)
A = Subobject(S, X=[3,4,5])

@withmodel 𝒞 (¬,~,⊤) begin 
  @test ¬A |> force == Subobject(ι₂)
  @test ¬Subobject(ι₂) |> force == Subobject(ι₁)
  @test ~A |> force == ⊤(S) |> force
end 

end # module
