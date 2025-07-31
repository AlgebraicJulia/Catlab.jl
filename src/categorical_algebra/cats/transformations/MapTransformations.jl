module MapTransformations 
export FinTransformationMap

using StructEquality
import GATlab: op

using ...Categories, ...FinCats, ...Functors, ...FinFunctors
using ..Transformations
using ...FinFunctors: mappairs
import ..Transformations: component, components, codom, FinTransformation, do_compose, do_composeH

# Mapping-based transformations
#------------------------------

""" Natural transformation with components given by explicit mapping.
"""
@struct_hash_equal struct FinTransformationMap{C<:FinCat,D<:Cat,
    Dom<:FinDomFunctor{C,D},Codom<:FinDomFunctor,Comp} <: FinTransformation{C,D,Dom,Codom}
  components::Comp
  dom::Dom
  codom::Codom
end

function FinTransformation(components::Union{AbstractVector,AbstractDict},
                           F::FinDomFunctor, G::FinDomFunctor)
  C, D = check_transformation_domains(F, G)
  length(components) == length(ob_generators(C)) ||
    error("Incorrect number of components in $components for domain category $C")
  components = mappairs(x -> ob_key(C,x), f -> hom(D,f), components)
  FinTransformationMap(components, F, G)
end

component(α::FinTransformationMap, x) = α.components[ob_key(dom_ob(α), x)]
components(α::FinTransformationMap) = α.components

op(α::FinTransformationMap) = FinTransformationMap(components(α),
                                                   op(codom(α)), op(dom(α)))

function do_compose(α::FinTransformationMap, β::FinTransformation)
  F = dom(α)
  D = codom(F)
  FinTransformationMap(mapvals(α.components, keys=true) do c, f
                         compose(D, f, component(β, c))
                       end, F, codom(β))
end

function do_composeH(F::FinDomFunctorMap, β::Transformation)
  G, H = dom(β), codom(β)
  FinTransformationMap(mapvals(c -> component(β, c), F.ob_map),
                       compose(F, G), compose(F, H))
end

function do_composeH(α::FinTransformationMap, H::Functor)
  F, G = dom(α), codom(α)
  FinTransformationMap(mapvals(f->hom_map(H,f),α.components),
                      compose(F, H), compose(G, H))
end

function Base.show(io::IO, α::FinTransformationMap)
  print(io, "FinTransformation(")
  show(io, components(α))
  print(io, ", ")
  Categories.show_domains(io, α, recurse=false)
  print(io, ", ")
  Categories.show_domains(io, dom(α))
  print(io, ")")
end


end # module
