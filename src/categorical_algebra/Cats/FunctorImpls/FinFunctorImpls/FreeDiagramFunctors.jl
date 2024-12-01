module FreeDiagramFunctors 
export FreeDiagramFunctor, diagram

using StructEquality

using GATlab
using .....Theories: ob, hom
using ...Paths: Path
using ...Categories: Category, TypeCat, FinCat, Cat, obtype, homtype, FreeCatGraph, PathCat
using ...FreeDiagrams: FreeDiagram
using ..FinFunctors: FinDomFunctorImpl, ThFinDomFunctor
import ..FinFunctors: FinDomFunctor

""" 
Wrapper type to interpret `FreeDiagram` as a `FinDomFunctor`.

A codom category tells us how to turn paths of homs into composite homs.
Domain is a FinCatGraph
"""
@struct_hash_equal struct FreeDiagramFunctor{CO,CH} <:
    FinDomFunctorImpl{Int,CO,Path{Int,Int},CH,Int}
  diagram::FreeDiagram{CO,CH}
  codom::Category
  function FreeDiagramFunctor(d::FreeDiagram{O,H}, c::Category) where {O,H}
    CO, CH = obtype(c), homtype(c)
    O <: CO || error("Bad Ob $O ≮ $CO")
    H <: CH || error("Bad Hom $H ≮ $CH")
    new{O,H}(d, c)
  end
end

GATlab.getvalue(f::FreeDiagramFunctor) = f.diagram
diagram(f::FreeDiagramFunctor) = f.diagram

# FinDomFunctor instance
########################

@instance ThFinDomFunctor{Int,CO,Path{Int,Int},CH,Int, FinCat, Category
                          } [model::FreeDiagramFunctor{CO,CH}
                            ] where {CO,CH} begin 

  dom() = FinCat(FreeCatGraph(getvalue(getvalue(model))))

  codom() = model.codom

  ob_map(x::Int)::CO = ob(model.diagram, x)

  gen_map(f::Int)::CH = hom(model.diagram, f)
end

# Convenience constructors
##########################
FinDomFunctor(diagram::FreeDiagram, codom::Cat) =
  FinDomFunctor(FreeDiagramFunctor(diagram, codom))

end # module
