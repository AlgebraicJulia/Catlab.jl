module SetCLimits 

using GATlab
using ...BasicSets.Sets: AbsSet
using ...BasicSets.SetFunctions: SetC, SetFunction
using ....Theories: ThCartesianCategory
using ...Cats.Limits: @cartesian_monoidal_instance

# Category of sets
##################

@cartesian_monoidal_instance AbsSet SetFunction SetC

end # module