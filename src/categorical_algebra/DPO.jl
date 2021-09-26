module DPO
export rewrite, rewrite_match, pushout_complement, can_pushout_complement,
  id_condition, dangling_condition, open_rewrite

using ...Theories
using ..FinSets, ..CSets, ..FreeDiagrams, ..Limits
using ..FinSets: id_condition
using ..CSets: dangling_condition
using ..StructuredCospans: StructuredMultiCospanHom, StructuredMulticospan, openrule

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

"""
Helper function for open_pushout_complement
Invert one (iso) component of an ACSetTransformation (given by s)
"""
function invert(f::ACSetTransformation,s::Symbol)::ACSetTransformation
  d = Dict([s=>Base.invperm(collect(f[s]))])
  return ACSetTransformation(codom(f), dom(f); d...)
end

"""References made to open pushout complement figure in CALCO paper"""
function open_pushout_complement(
    rule::openrule,
    G::StructuredMulticospan{L_},
    m::StructuredMultiCospanHom)::openrule where L_
  # Unpack data
  ob = L_.parameters[1]
  L, R = rule.data;
  I, R_ = dom(R), codom(R);

  # Validate
  L.src == R.src || error("bad rule: L,R mismatch")

  # gets green arrows (vertical, leftward pointing)
  pcs = [pushout_complement(a,b) for (a,b) in zip(L.maps, m.maps)];

  # gets purple arrows
  pos = [legs(pushout(a,b)) for (a, (b, _)) in zip(R.maps, pcs)];

  # gets red arrows
  posK = [compose(invert(b, ob), a, pcs[1][1]) for (a, (b, _))
          in zip(legs(I), pcs[2:end])]
  posH = [compose(invert(b, ob), a, pos[1][1]) for (a, (b, _))
          in zip(legs(R_), pos[2:end])]

  # Reassemble resulting data into span of multicospans
  feetK = [FinSet(nparts(codom(b), ob)) for (b,_) in pcs[2:end]]
  feetH = [FinSet(nparts(codom(b), ob)) for (b,_) in pos[2:end]]
  K = StructuredMulticospan{L_}(Multicospan(posK), feetK)
  H = StructuredMulticospan{L_}(Multicospan(posH), feetH)
  new_L = StructuredMultiCospanHom(K, G, ACSetTransformation[pc[2] for pc in pcs])
  new_R = StructuredMultiCospanHom(K, H, ACSetTransformation[po[2] for po in pos])
  return openrule(Span(new_L, new_R))
end

function open_rewrite(
  rule::openrule,
  G::StructuredMulticospan{L_},
  m::StructuredMultiCospanHom)::StructuredMulticospan{L_} where L_
  return right(open_pushout_complement(rule, G, m).data).tgt
end

end