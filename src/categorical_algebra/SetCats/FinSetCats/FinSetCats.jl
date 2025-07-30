export TabularLimit, VarSet, VarFunction, LooseVarFunction,
  JoinAlgorithm, SmartJoin, NestedLoopJoin, SortMergeJoin, HashJoin,
  SubFinSet, SubOpBoolean

using StructEquality
using DataStructures: OrderedDict, IntDisjointSets, union!, find_root!
import StaticArrays
using StaticArrays: StaticVector, SVector, SizedVector, similar_type
using Reexport 

using ACSets

@reexport using ..SetCats
using ....Theories, ....Graphs, ....BasicSets
import ....Theories: Ob, meet, ∧, join, ∨, top, ⊤, bottom, ⊥, ⋅, dom, codom,
  compose
using ...Cats
using ...Cats.FinFunctors: dicttype
import ...Cats: ob, hom, dom, codom, compose, id, ob_map, hom_map, 
                force, ob_generators, hom_generators, ob_generator,
                ob_generator_name, graph, is_discrete, limit, colimit, 
                universal, do_compose


# For now, we do not preserve or compose indices, only the function vectors.
do_compose(f::Union{FinFunctionVector,IndexedFinFunctionVector},
                g::Union{FinDomFunctionVector,IndexedFinDomFunctionVector}) =
  FinDomFunctionVector(g.func[f.func], codom(g))

do_compose(f::FinFunctionDict{K,D}, g::FinDomFunctionDict) where {K,D} =
  FinDomFunctionDict(dicttype(D)(x => g.func[y] for (x,y) in pairs(f.func)),
                     codom(g))

do_compose(f::FinFunctionVector, g::FinDomFunctionVector) =
  FinDomFunctionVector(g.func[f.func], codom(g))

# Note: Cartesian monoidal structure is implemented generically for Set but
# cocartesian only for FinSet.
@cocartesian_monoidal_instance FinSet FinFunction

Ob(C::FinCat{Int}) = FinSet(length(ob_generators(C)))

Ob(F::Functor{<:FinCat{Int}}) = FinDomFunction(collect_ob(F), Ob(codom(F)))


