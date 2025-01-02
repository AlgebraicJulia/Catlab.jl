module MapTrans 

export is_natural, FinTransformationMap
using StructEquality
using GATlab

using ...Categories: Cat
using ...Functors: Functor
using ...FinCats: FinCat
using ...FinFunctors: FinDomFunctor, mapvals

using ..NatTrans: ThTransformation, Transformation


""" A natural transformation whose domain category is finitely generated.

This type is for natural transformations ``α: F ⇒ G: C → D`` such that the
domain category ``C`` is finitely generated. Such a natural transformation is
given by a finite amount of data (one morphism in ``D`` for each generating
object of ``C``) and its naturality is verified by finitely many equations (one
equation for each generating morphism of ``C``).
"""
# const FinTransformation{C<:FinCat,D<:Cat,Dom<:FinDomFunctor,Codom<:FinDomFunctor} =
#   Transformation{C,D,Dom,Codom}

FinTransformation(F, G; components...) = FinTransformation(components, F, G)

""" Components of a natural transformation.
"""
components(α::Transformation) =
  make_map(x -> component(α, x), ob_generators(dom_ob(α)))

""" Is the transformation between `FinDomFunctors` a natural transformation?

This function uses the fact that to check whether a transformation is natural,
it suffices to check the naturality equations on a generating set of morphisms
of the domain category. In some cases, checking the equations may be expensive
or impossible. When the keyword argument `check_equations` is `false`, only the
domains and codomains of the components are checked.

See also: [`is_functorial`](@ref).
"""
function is_natural(α::Transformation; check_equations::Bool=true)
  # THROW AN ERROR IF THE TRANSFORMATION IS NOT A FINTRANSFORMATION?
  F, G = dom(α), codom(α)
  C, D = dom(F), codom(F) # == dom(G), codom(G)
  all(ob_generators(C)) do c
    α_c = α[c]
    dom(D, α_c) == ob_map(F,c) && codom(D, α_c) == ob_map(G,c)
  end || return false

  if check_equations
    all(hom_generators(C)) do f
      Ff, Gf = hom_map(F,f), hom_map(G,f)
      α_c, α_d = α[dom(C,f)], α[codom(C,f)]
      is_hom_equal(D, compose(D, α_c, Gf), compose(D, Ff, α_d))
    end || return false
  end

  true
end

function check_transformation_domains(F::Functor, G::Functor)
  # XXX: Equality of TypeCats is too strict, so for now we are punting on
  # (co)domain checks in that case.
  C, C′ = dom(F), dom(G)
  (C isa TypeCat && C′ isa TypeCat) || C == C′ ||
    error("Mismatched domains in functors $F and $G")
  D, D′ = codom(F), codom(G)
  (D isa TypeCat && D′ isa TypeCat) || D == D′ ||
    error("Mismatched codomains in functors $F and $G")
  (C, D)
end

# Mapping-based transformations
#------------------------------

""" Natural transformation with components given by explicit mapping.
"""
@struct_hash_equal struct FinTransformationMap{C<:FinCat,D<:Cat,
    Dom<:FinDomFunctor{C,D},Codom<:FinDomFunctor,Comp}
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
# Composition of Transformations 
#
# function Categories.do_compose(α::FinTransformationMap, β::FinTransformation)
#   F = dom(α)
#   D = codom(F)
#   FinTransformationMap(mapvals(α.components, keys=true) do c, f
#                          compose(D, f, component(β, c))
#                        end, F, codom(β))
# end

# function Categories.do_composeH(F::FinDomFunctorMap, β::Transformation)
#   G, H = dom(β), codom(β)
#   FinTransformationMap(mapvals(c -> component(β, c), F.ob_map),
#                        compose(F, G), compose(F, H))
# end

# function Categories.do_composeH(α::FinTransformationMap, H::Functor)
#   F, G = dom(α), codom(α)
#   FinTransformationMap(mapvals(f->hom_map(H,f),α.components),
#                       compose(F, H), compose(G, H))
# end

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