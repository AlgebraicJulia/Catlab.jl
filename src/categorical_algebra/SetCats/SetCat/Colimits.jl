module SetColimits 

using .....BasicSets: TypeSet
using ....Cats: SingletonDiagram, SpecializeColimit
import ....Cats: colimit

colimit(Xs::SingletonDiagram{<:TypeSet}) = colimit(Xs, SpecializeColimit())

end # module