module TestLabeledCSetLimits 

using Catlab, Test

const WG = WeightedGraph{Symbol}

A = @acset WG begin 
  V=1;E=2;Weight=1;src=1;tgt=1;weight=[AttrVar(1),:X] 
end
B = @acset WG begin V=1;E=2;Weight=1;src=1;tgt=1;weight=[:X, :Y] end

𝒞 = infer_acset_cat(A)
CM = TypedCatWithCoproducts(𝒞)
C = @withmodel CM (⊕) begin
  B ⊕ @acset WG begin V=1 end
end


AC = homomorphism(A,C; initial=(E=[1,1],))
BC = CSetTransformation(B,C; V=[1],E=[1,2], Weight=[:X])
@test all(is_natural,[AC,BC])
p1, p2 = product(A,A; cset=true);
X = @acset WG begin V=1;E=2;Weight=1;src=1;tgt=1;weight=[:X, :X] end
@test nparts(apex(product(X,X;cset=true)),:Weight) == 1

# Pullback in Graph from (Reyes et al 2004, p. 53), again
g0, g1, g2 = WG.([2,3,2])
add_edges!(g0, [1,1,2], [1,2,2]; weight=[:X,:Y,:Z])
add_edges!(g1, [1,2,3], [2,3,3]; weight=[:Y,:Z,AttrVar(add_part!(g1,:Weight))])
add_edges!(g2, [1,2,2], [1,2,2]; weight=[AttrVar(add_part!(g2,:Weight)), :Z,:Z])
ϕ = homomorphism(g1, g0) |> CSetTransformation
ψ = homomorphism(g2, g0; initial=(V=[1,2],)) |> CSetTransformation
@test is_natural(ϕ) && is_natural(ψ)
lim = pullback(ϕ, ψ)
@test nv(ob(lim)) == 3
@test sort!(collect(zip(src(ob(lim)), tgt(ob(lim))))) ==
  [(2,3), (2,3), (3,3), (3,3)]
@test is_natural(proj1(lim)) && is_natural(proj2(lim))
# Example: "Reflexive graphs" where reflexive edges have weight -1
A = @acset WeightedGraph{Float64} begin V=2; E=3; 
  src=[1, 2, 1]; tgt=[1, 2, 2]; weight=[-1, -1, 5] 
end
B = @acset WeightedGraph{Float64} begin V=3; E=5; 
  src=[1, 2, 3, 1, 2]; tgt=[1, 2, 3, 2, 3]; weight=[-1, -1, -1, 2, 3] 
end

# 1. Stratification with LooseACSetTransformation
C_nothing =  @acset WeightedGraph{Nothing} begin V=1; E=2; Weight=2
  src=1; tgt=1; weight=[nothing,nothing]
end
AC_nothing = LooseACSetTransformation(
    (V=[1, 1], E=[1, 1, 2],), (Weight=(_->nothing),), A, C_nothing)
BC_nothing = LooseACSetTransformation(
    (V=[1, 1, 1], E=[2, 2, 2, 1, 1],), (Weight=(_->nothing),), B, C_nothing)
res = apex(pullback(AC_nothing, BC_nothing))
@test nparts(res, :E) == 7
@test eltype(res[:weight]) == Tuple{Float64, Float64}

# 2. Stratification with CSetTransformations
C = @acset WeightedGraph{Float64} begin V=1; E=2; Weight=2
  src=1; tgt=1; weight=[3.1415, 2.71]
end

AC = CSetTransformation(A, C; V=[1, 1], E=[1, 1, 2])
BC = CSetTransformation(B, C; V=[1, 1, 1], E=[2, 2, 2, 1, 1])
ABC = pullback(AC,BC);
expected = @acset WeightedGraph{Float64} begin V=6; E=7; Weight=3; 
  src=[1,1,2,3,3,4,5]; tgt=[2,3,4,4,5,6,6]; weight=AttrVar.([1,2,2,1,3,3,1]) 
end
@test is_isomorphic(apex(ABC),expected)

# 3. Apply commutative monoid to attrs
ABC = pullback(AC, BC; attrfun=(weight=prod,))
expected = @acset WeightedGraph{Float64} begin V=6; E=7;
  src=[1,1,2,3,3,4,5]; tgt=[2,3,4,4,5,6,6]; weight=[-5,-2,-2,-5,-3,-3,-5]
end
@test is_isomorphic(apex(ABC),expected)

end # module
