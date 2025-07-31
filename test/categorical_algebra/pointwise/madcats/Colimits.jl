module TestMADColimits


using Test, Catlab
using Catlab.CategoricalAlgebra.Pointwise.LimitsColimits.Colimits: pointwise_colimit

# MAD Graphs
#############
@acset_type MGraph(SchGraph, part_type=BitSetParts) <: HasGraph
const Grph = ACSetCategory(MADCSetCat(MGraph()))

G1 = MGraph(1)
i1 = id[Grph](G1)

pushout[Grph](i1,i1)

end # module
