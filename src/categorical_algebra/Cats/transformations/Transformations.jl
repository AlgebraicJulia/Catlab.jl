export FinTransformation, components, is_natural, 
       do_composeH, check_transformation_domains

using StructEquality
import GATlab: op

using ..Cats
import ..Functors: do_compose

# Natural transformations
#########################

""" A natural transformation whose domain category is finitely generated.

This type is for natural transformations ``α: F ⇒ G: C → D`` such that the
domain category ``C`` is finitely generated. Such a natural transformation is
given by a finite amount of data (one morphism in ``D`` for each generating
object of ``C``) and its naturality is verified by finitely many equations (one
equation for each generating morphism of ``C``).
"""
const FinTransformation{C<:FinCat,D<:Cat,Dom<:FinDomFunctor,Codom<:FinDomFunctor} =
  Transformation{C,D,Dom,Codom}

FinTransformation(F, G; components...) = FinTransformation(components, F, G)

""" Components of a natural transformation.
"""
components(α::FinTransformation) =
  make_map(x -> component(α, x), ob_generators(dom_ob(α)))

""" Is the transformation between `FinDomFunctors` a natural transformation?

This function uses the fact that to check whether a transformation is natural,
it suffices to check the naturality equations on a generating set of morphisms
of the domain category. In some cases, checking the equations may be expensive
or impossible. When the keyword argument `check_equations` is `false`, only the
domains and codomains of the components are checked.

See also: [`is_functorial`](@ref).
"""
function is_natural(α::FinTransformation; check_equations::Bool=true)
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

function do_composeH end 
