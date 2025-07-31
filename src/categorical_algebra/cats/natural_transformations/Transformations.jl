
export co, Cat2, component, dom_ob, codom_ob, is_natural, Transformation, 
       components, ThTransformation, FinTransformation, naturality_failures,
       check_transformation_domains

using StructEquality
using Reexport

using GATlab
import GATlab: getvalue

using ....Theories: ThCategory2
import .ThCategory2: dom, codom, compose, ⋅, ∘, id, composeH, *
using ..Cats
import ..Cats: validate

# Natural transformations
#########################

# The equations that come with this will be less tedious to do when colimits 
# of GATs are a thing
"""
`DomFun` and `CodFun` should be sent to AbsFunctor
"""
@theory ThTransformation begin
  DO::TYPE; CH::TYPE; DomFun::TYPE; CodFun::TYPE
  dom()::DomFun 
  codom()::CodFun
  component(x::DO)::CH
end

ThTransformation.Meta.@typed_wrapper Transformation

const FinTransformation{DO,CH,CodFun} = Transformation{DO,CH,<:FunctorFinDom, CodFun}


function validate(i::Transformation)
  F, G = ThTransformation.dom(i), ThTransformation.codom(i)
  validate(F)
  validate(G)
  tF, tG = typeof.([F,G])
  C, D = check_transformation_domains(F, G)
  DO,CH,DF,CF,Ob,Hom = impl_type.([i,i,i,i,C,D], [:DO,:CH,:DomFun,:CodFun,:Ob,:Hom])
  Ob == DO || error("Bad dom ob type: $(Ob) ≠ $DO")
  Hom == CH || error("Bad codom hom type: $(Hom) ≠ $CH")
  tF <: DF || error("Bad dom fun type: $(tF) ≠ $DF")
  tG <: CF || error("Bad codom fun type: $(tG) ≠ $CF")
  i
end

@inline Base.getindex(α::Transformation, c) = component(α, c)

""" Domain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``C``.
"""
dom_ob(α::Transformation) = dom(dom(α)) # == dom(codom(α))

""" Codomain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``D``.
"""
codom_ob(α::Transformation) = codom(dom(α)) # == codom(codom(α))

""" Is the transformation between functors a natural transformation?

This function uses the fact that to check whether a transformation is natural,
it suffices to check the naturality equations on a generating set of morphisms
of the domain category. In some cases, checking the equations may be expensive
or impossible. When the keyword argument `check_equations` is `false`, only the
domains and codomains of the components are checked.

See also: [`is_functorial`](@ref).
"""
function is_natural(α::Transformation; check_equations::Bool=true)
  isempty(naturality_failures(α; check_equations))
end

function naturality_failures(α::Transformation; check_equations::Bool=true)
  failures = []
  F, G = dom(α), codom(α)
  F isa FunctorFinDom || error(
    "Can only check naturality for finitely presented domains: $F")

  C, D = dom(F), codom(F) # == dom(G), codom(G)

  for c in ob_generators(C)
    α_c = α[c]
    dα, cdα, Fc, Gc  = dom(D, α_c), codom(D, α_c), ob_map(F,c), ob_map(G,c)
    dα == Fc  || push!(failures, (:dom, c, dα, Fc))
    cdα == Gc || push!(failures, (:codom, c, cdα, Gc))
  end

  if check_equations
    for f in hom_generators(C)
      Ff, Gf = gen_map(F,f), gen_map(G,f)
      α_c, α_d = α[src(C,f)], α[tgt(C,f)]
      # KBTODO add is_hom_equal to ThCategory interface
      αc_Gf = force(compose(D, α_c, Gf)) 
      Ff_αd = force(compose(D, Ff, α_d)) 
      αc_Gf == Ff_αd || push!(failures, (:eq, f, αc_Gf, Ff_αd))
    end
  end

  failures
end

""" Components of a natural transformation.
"""
components(α::Transformation) =
  make_map(x -> component(α, x), ob_generators(dom_ob(α)))

function check_transformation_domains(F::FunctorFinDom, G::FunctorFinDom)
  # XXX: Equality of TypeCats is too strict, so for now we are punting on
  # (co)domain checks in that case.
  (C, C′), (D, D′) = (Cs, Ds) = (dom.([F,G]), codom.([F,G]))
  vC, vC′, vD, vD′ = getvalue.([Cs; Ds])
  (vC isa TypeCat && vC′ isa TypeCat) || vC == vC′ ||
    error("Mismatched domains in functors $F and $G")
  (vD isa TypeCat && vD′ isa TypeCat) || vD == vD′ ||
    error("Mismatched codomains in functors $F and $G")
  (C, D)
end
