
const WG = WeightedGraph

w1,w2,w3 = ws = [WG{x}() for x in [Symbol,Bool,Int]]
[add_parts!(w, :Weight, 2) for w in ws]
rem_part!(w1, :Weight, 1)

# Construct Tight/Loose ACSet Transformations
#--------------------------------------------
f21 = LooseVarFunction{Bool,Symbol}([AttrVar(1),AttrVar(1)], x->Symbol(x), FinSet(1))
t21 = ACSetTransformation(Dict(:Weight=>f21), w2, w1) 
@test t21 isa LooseACSetTransformation
t22 = ACSetTransformation(Dict(:Weight=>[AttrVar(1),false]), w2, w2)


bool_to_sym(x::Bool)::Symbol = x ? :A : :B

f21 = LooseVarFunction{Bool,Symbol}([AttrVar(1),:X], bool_to_sym, FinSet(1))
l21 = ACSetTransformation((Weight = f21,), w2, w1)

t32 = LooseVarFunction{Int,Bool}([AttrVar(2),false], iseven,FinSet(2))
l32 = ACSetTransformation((Weight = t32,), w3, w2)
@test all(is_natural,[l21,l32])