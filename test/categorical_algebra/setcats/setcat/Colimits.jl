module TestSetCColimits

using Catlab, Test

const 𝒞 = SetC()

# Trivial coproduct.
####################
TC = TypeCat(𝒞)
colim = colimit[TC](SingletonDiagram(SetOb(Int)))
@test ob(colim) == SetOb(Int)

f = SetFunction(string, SetOb(Int), SetOb(String))
@test universal[TC](colim, SMulticospan{1}(f)) === f

end # module
