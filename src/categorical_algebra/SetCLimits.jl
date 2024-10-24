module SetCLimits 

using GATlab
using ..Sets: AbsSet
using ..SetFunctions: SetC, SetFunction
using ...Theories: ThCartesianCategory
using ..Limits: @cartesian_monoidal_instance

# Category of sets
##################

@cartesian_monoidal_instance AbsSet SetFunction SetC

end # module