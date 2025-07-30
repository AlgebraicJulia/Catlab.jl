module TestVarACSetColimits 

using Catlab, Test

const WG = WeightedGraph

A = @acset WG{Bool} begin V=1;E=2;Weight=2;src=1;tgt=1;weight=[AttrVar(1),true] end

# CREATE 
@test dom(create(A)) == WG{Bool}()

# COPRODUCT
diagram = DiscreteDiagram([A,A])
AA = coproduct([A,A])
@test apex(AA)[:weight] == [AttrVar(1),true,AttrVar(3),true]
@test legs(AA)[2] isa TightACSetTransformation
@test collect(legs(AA)[2][:Weight]) == AttrVar.(3:4)

X = @acset WG{Bool} begin V=1;E=1;Weight=2;src=1;tgt=1;weight=[true] end
f′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(1)],))
g′ = homomorphism(A, X; initial=(Weight=[true,AttrVar(2)],))
fg = universal(AA, Cospan(f′,g′))

# PUSHOUTS
V = @acset WG{Bool} begin Weight=1 end
f = ACSetTransformation(Dict(:Weight=>[AttrVar(1)]), V, A)
g = ACSetTransformation(Dict(:Weight=>[AttrVar(2)]), V, A)

clim = colimit(Span(f,g));
@test all(is_natural, legs(clim))
@test collect(legs(clim)[2][:Weight]) == AttrVar.([3,1]) # not [3,4] anymore

fg = universal(clim, Cospan(f′,g′))

f = ACSetTransformation(Dict(:Weight=>[AttrVar(1)]), V, A)
g = ACSetTransformation(Dict(:Weight=>[true]), V, A)

clim = colimit(Span(f,g));
@test all(is_natural, legs(clim))
@test apex(clim)[:weight] == [true,true,AttrVar(2),true]
@test collect(legs(clim)[1][:Weight]) == [true,AttrVar(1)]

# Abstracting
X = @acset WG{Bool} begin 
  V=1; E=2; Weight=1; src=1; tgt=1; weight=[AttrVar(1), true]
end
h = abstract_attributes(X)
@test nparts(dom(h), :Weight) == 2
@test codom(h) == X
@test is_natural(h)

# Mutation of codom of A->X should not modify domain
rem_part!(X, :E, 2)
@test nparts(dom(h), :E) == 2

end # module
