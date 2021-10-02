module DPO
export rewrite, rewrite_match, pushout_complement, id_condition,
  dangling_condition, open_rewrite, open_rewrite_match

using ...Theories
using ..FinSets, ..CSets, ..FreeDiagrams, ..Limits
using ..FinSets: id_condition
using ..CSets: dangling_condition
using ..StructuredCospans: StructuredMultiCospanHom, StructuredMulticospan,
  openrule, open_homomorphisms, can_open_pushout_complement

# ACSet rewriting
#################

"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite.
"""
function rewrite_match(L::ACSetTransformation, R::ACSetTransformation,
                       m::ACSetTransformation)::ACSet
  dom(L) == dom(R) || error("Rewriting where L, R do not share domain")
  codom(L) == dom(m) || error("Rewriting where L does not compose with m")
  (k, _) = pushout_complement(L, m)
  l1, _ = pushout(R, k)
  return codom(l1)
end

"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet,
where a match morphism is found automatically. If multiple
matches are found, a particular one can be selected using
`m_index`.
"""
function rewrite(L::ACSetTransformation, R::ACSetTransformation,
                 G::ACSet; monic::Bool=false, m_index::Int=1
                 )::Union{Nothing,ACSet}
  ms = filter(m->can_pushout_complement(L, m),
              homomorphisms(codom(L), G, monic=monic))
  if 0 < m_index <= length(ms)
    rewrite_match(L, R, ms[m_index])
  else
    nothing
  end
end

# Structured multicospan rewriting
##################################

"""
Helper function for open_pushout_complement
Invert one (presumed iso) component of an ACSetTransformation (given by s)
"""
function invert(f::ACSetTransformation,s::Symbol)::ACSetTransformation
  d = Dict([s=>Base.invperm(collect(f[s]))])
  return ACSetTransformation(codom(f), dom(f); d...)
end

"""
Initial data: 4 structured cospans + 3 cospan morphisms: μ, λ, ρ
     g
G₁₋ₙ --> G
↑    l  ↑ μ
L₁₋ₙ --> L
↑    i  ↑ λ
I₁₋ₙ --> I
↓    r  ↓ ρ
R₁₋ₙ --> R

Computed data: 2 new structured cospans + 4 cospan morphisms: γ, η, ik, rh

        G₁₋ₙ      G
          ↑    k  ↑ γ   ik
 I₁₋ₙ -> K₁₋ₙ  --> K    <-- I
          ↓    h  ↓ η   rh
 R₁₋ₙ -> H₁₋ₙ  --> H    <-- R

In the context of the legs of a multicospan, the indices 1-n refer to the n
legs of the cospan. In the context of a map of multicospans, there are 1-(n+1)
maps, with the first one designating the map of the apexes. Hence it can make
sense to have the elements: zip(legs, maps[2:end]) = [(legᵢ, mapᵢ), ...]
"""
function open_pushout_complement(
    rule::openrule,
    μ::StructuredMultiCospanHom)::openrule

  # Unpack data
  L_ = typeof(left(rule.data)).parameters[1];
  ob = L_.parameters[1]
  λ, ρ = rule.data;
  I, R, G = dom(ρ), codom(ρ), codom(μ);

  # Compute pushouts and pushout complements
  ik_γ = [pushout_complement(λᵢ,μᵢ) for (λᵢ, μᵢ) in zip(λ.maps, μ.maps)];
  rh_η = [legs(pushout(ρᵢ,ikᵢ)) for (ρᵢ, (ikᵢ, _)) in zip(ρ.maps, ik_γ)];
  rh, ik = rh_η[1][1], ik_γ[1][1]
  k = [compose(invert(ikᵢ, ob), iᵢ, ik) for (iᵢ, (ikᵢ, _))
       in zip(legs(I), ik_γ[2:end])]
  h = [compose(invert(rhᵢ, ob), r₍, rh) for (r₍, (rhᵢ, _))
       in zip(legs(R), rh_η[2:end])]

  # Reassemble resulting data into span of multicospans
  feetK = [FinSet(nparts(codom(ikᵢ), ob)) for (ikᵢ, _) in ik_γ[2:end]]
  feetH = [FinSet(nparts(codom(rhᵢ), ob)) for (rhᵢ, _) in rh_η[2:end]]
  K = StructuredMulticospan{L_}(Multicospan(k), feetK)
  H = StructuredMulticospan{L_}(Multicospan(h), feetH)
  maps_γ = ACSetTransformation[γᵢ for (_, γᵢ) in ik_γ]
  maps_η = ACSetTransformation[ηᵢ for (_, ηᵢ) in rh_η]
  γ = StructuredMultiCospanHom(K, G, maps_γ)
  η = StructuredMultiCospanHom(K, H, maps_η)
  return openrule(Span(γ, η))
end

"""
Extract the rewritten structured cospan from the induced rewrite rule
"""
function open_rewrite_match(
    rule::openrule, m::StructuredMultiCospanHom)::StructuredMulticospan
  right(open_pushout_complement(rule, m).data).tgt
end

"""
Apply a rewrite rule to a structured multicospan, where a matching cospan
homomorphism is found automatically. If multiple matches are found, a particular
one can be selected using `m_index`. Returns `nothing` if none are found.
"""
function open_rewrite(rule::openrule, G::StructuredMulticospan;
                      monic::Bool=false, m_index::Int=1)::StructuredMulticospan

  ms = filter(m->can_open_pushout_complement(left(rule.data), m),
              open_homomorphisms(left(rule.data).tgt, G, monic=monic))
  if 0 < m_index <= length(ms)
    open_rewrite_match(rule, ms[m_index])
  else
    nothing
  end
end
end # module