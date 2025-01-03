module TestVarACSetHomSearch 

using Catlab, Test


# AttrVar constraints (monic and no_bind)
#----------------------------------------
@present SchLSet(FreeSchema) begin X::Ob; D::AttrType; f::Attr(X,D) end
@acset_type LSet(SchLSet){Symbol}

# Simple example
A = @acset LSet begin X=2; D=2; f=AttrVar.(1:2) end
B = @acset LSet begin X=1; D=1; f=[AttrVar(1)] end
@test isempty(homomorphisms(A, B; monic=[:D]))
@test length(homomorphisms(B, A; monic=[:D])) == 2
@test length(homomorphisms(A, A; monic=[:D])) == 2

# More complicated example
G = @acset LSet begin X=3; D=2; f=[:a; AttrVar.(1:2)] end
H = @acset LSet begin X=4; D=3; f=[:a, :b, AttrVar.(1:2)...] end

# X₂ and X₃ in G can go to any of the 4 Xs in H
@test length(homomorphisms(G, H)) == 16

G′ = copy(G)
add_part!(G′, :D) # add a free floating variable to domain

# If we don't put any constraints on the free var, error b/c of infinite homs
@test_throws ErrorException homomorphisms(G′, H)

# All attrvars going to :b forces all Xs going to X₂
@test length(homomorphisms(G′, H; initial=(D=[:b,:b,:b],),)) == 1

# If we just force the free variable to go to a fixed place, it's the same as before
@test length(homomorphisms(G′, H; initial=(D=Dict(3=>:b),))) == 16
@test length(homomorphisms(G′, H; initial=(D=Dict(3=>AttrVar(1)),))) == 16

# [2,1] and [1,2] for where AttrVars go
@test length(homomorphisms(G, H; monic=[:D])) == 2 
# free var forced to go to D₃
@test length(homomorphisms(G′, H; monic=[:D])) == 2 
# D₁ D₂ go to any of the 4 Xs. D₃ goes to any of the 3 Ds
@test length(homomorphisms(G′, H; no_bind=[:D])) == 4*4*3

end # module
