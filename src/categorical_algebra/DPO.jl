module DPO
export rewrite, rewrite_match, rewrite_match_maps, pushout_complement, can_pushout_complement,
  id_condition, dangling_condition

using ...Theories
using ..FinSets, ..CSets, ..FreeDiagrams, ..Limits
using ..FinSets: id_condition
using ..CSets: dangling_condition

"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite.
              l   r
           L <- I -> R
         m ↓    ↓    ↓
           G <- K -> H

Returns:
- The morphisms I->K, K->G (produced by pushout complement), followed by
  R->H, and K->H (produced by pushout)
"""
function rewrite_match_maps(L, R, m)
  dom(L) == dom(R) || error("Rewriting where L, R do not share domain")
  codom(L) == dom(m) || error("Rewriting where L does not compose with m")
  (ik, kg) = pushout_complement(L, m)
  rh, kh = pushout(R, ik)
  return ik, kg, rh, kh
end

"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite. Return the rewritten ACSet.
"""
rewrite_match(L, R, m) = codom(rewrite_match_maps(L, R, m)[4])


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

end
