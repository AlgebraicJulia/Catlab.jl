module DPO
export rewrite, rewrite_match, pushout_complement, can_pushout_complement,
  id_condition, dangling_condition, sesqui_pushout_rewrite_data,
  sesqui_pushout_rewrite, final_pullback_complement,
  partial_map_classifier_universal_property, partial_map_classifier_eta,
  rewrite_match_maps

using ...Theories
using ..FinSets, ..CSets, ..FreeDiagrams, ..Limits
using ..FinSets: id_condition
using ..CSets: dangling_condition
using DataStructures

# Double-pushout rewriting
##########################

"""
Apply a DPO rewrite rule (given as a span, L<-I->R) to a ACSet
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
function rewrite_match_maps(
    L::ACSetTransformation, R::ACSetTransformation, m::ACSetTransformation
    )::Tuple{ACSetTransformation,ACSetTransformation,
             ACSetTransformation,ACSetTransformation}
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
rewrite_match(L::ACSetTransformation, R::ACSetTransformation,
  m::ACSetTransformation)::ACSet = codom(rewrite_match_maps(L, R, m)[4])


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

# Sesqui-pushout rewriting
##########################

"""
The specification for the following functions comes from:
  - 'Concurrency Theorems for Non-linear Rewriting Theories'
     - for final pullback complement and sesqui-pushout rewriting
  - 'AGREE - Algebraic Graph Rewriting with Controlled Embedding'
     - for partial map classifier (a functor T and natural transformation η)
"""

"""
A functor T, playing the role of Maybe in Set, but generalized to C-Sets. This
function specifies what T does on objects. The key properties of this functor:
  1. for all X ∈ Ob(C), η(X):X⟶T(X) is monic.
                     m   f                                    ϕ(m,f)
  2. for each span A ↩ X → B, there exists a unique morphism A ⟶ T(B)
     such that (m,f) is the pullback of ϕ(m,f),η(B))

Not only do we add an extra element to each component of the C-Set, but we need
to consider the possibility that a component (with n outgoing morphisms) has any
combination of the targets of those morphisms deleted (like the subobject
classifier, there are different *ways* for something to be deleted).

For example, in Graph, an edge can be deleted that goes between any two vertices
of the graph. We can't map all deleted edges to the same point in T(E) (if we're
going to satisfy that desired property #2), so we need an extra edge in T(E) for
every possibility (from V1 to V2, from V1 to V3, ..., from [Deleted] to V1, ...,
from V2 to [Deleted], ... from [Deleted] to [Deleted]), where [Deleted] is our
name for the extra element added to T(V).

                    [src]     [tgt]
Thus, T(E) ≅ |E| + (|V|+1) × (|V|+1).

In general, T(X) ≅ |X| + ∏ₕ(|codom(h)|+1) for each outgoing morphism h::X⟶Y
- the |X| corresponds to the 'real' elements of X
- the second term corresponds to the possible ways an X can be deleted.
"""
function partial_map_functor_ob(x::StructCSet{S})::StructCSet where {S}
  res = deepcopy(x)
  hdata = collect(zip(hom(S), dom(S), codom(S)))
  extra_data = Dict{Symbol, Vector{Dict{Symbol, Int}}}()
  for o in ob(S)
    extra_data[o] = Dict{Symbol, Int}[]
    homs_cds = [(h,cd) for (h,d,cd) in hdata if d==o] # outgoing morphism data
    if !isempty(homs_cds)
      homs, cds = collect.(zip(homs_cds...))
      combdata = collect(Iterators.product([1:nparts(x,cd)+1 for cd in cds]...))
      # We don't use the last element of this iterator (|X₁|+1,|X₂|+1,...)
      # corresponding to an element (and everything it points to) that's deleted
      # because it *is* the element added to each set (added below)
      for c in combdata[1:end-1]
        push!(extra_data[o], Dict{Symbol, Int}(zip(homs,c)))
      end
    end
  end
  # Add the extra element to each set
  copy_parts!(res, apex(terminal(typeof(x))))
  # Add the computed combination data
  for (k, vs) in extra_data
    for v in vs
      add_part!(res, k; v...)
    end
  end
  return res
end

"""
Because the functorial embedding of objects keeps a copy of the original data,
what to do with morphisms is just carry them along. Because our implementation
adds all of the additional stuff afterwards, index-wise, we can use literally
the same data for a morphism lifted from X⟶Y to T(X)⟶T(Y).

However, we still need to map the extra stuff in T(X) to the proper extra stuff
in T(Y).
"""
function partial_map_functor_hom(f::CSetTransformation{S}
    )::CSetTransformation where S
  X, Y = dom(f), codom(f)
  d, cd = partial_map_functor_ob.([X,Y])
  comps, mapping = [Dict{Symbol,Vector{Int}}() for _ in 1:2]
  hdata = collect(zip(hom(S),dom(S),codom(S)))

  for (k,v) in pairs(f.components)
    mapping[k] = vcat(collect(v), [nparts(Y, k)+1]) # map extra val to extra
  end

  for o in ob(S)
    comps[o] = Int[]
    homs_cds = [(h,cd) for (h,d,cd) in hdata if d==o]
    if !isempty(homs_cds)
      codom_data = collect.(zip([cd[h] for h in first.(homs_cds)]...))
    end
    for i in parts(d, o)
      if i <= length(mapping[o])
        push!(comps[o], mapping[o][i]) # use f for elements that are defined
      else
        # find what the extra element in T(Y) maps to (its outgoing morphisms)
        outdata = [mapping[cd][d[h][i]] for (h,cd) in (homs_cds)]
        # Find the element in T(Y) by iterating through its elements
        # Search in reverse order so that we hit the added-on element first, in
        # case there happens to be a 'real' element in Y that has the same data
        for (j, outdata_) in reverse(collect(enumerate(codom_data)))
          if outdata_ == outdata
            push!(comps[o], j)
            break
          end
        end
      end
    end
  end
  return CSetTransformation(d,cd;comps...)
end

"""
The natural injection from X ⟶ T(X)
"""
function partial_map_classifier_eta(x::StructCSet{S}
    )::CSetTransformation where {S}
  codom = partial_map_functor_ob(x)
  d = Dict([k=>collect(v) for (k,v) in pairs(id(x).components)])
  return CSetTransformation(x, codom; d...)
end



"""A partial function is induced by the following span:
                          m   f
                        A ↩ X → B

We compute ϕ(m,f): A ⟶ T(B) such that the following is a pullback square:
     f
  X  ⟶ B
m ↓     ↓ η(B)
  A  ⟶ T(B)
     ϕ

Essentially, ϕ sends elements of A to the 'real' values in T(B) when A is in
the subobject picked out by X. When A is 'deleted', it picks out the right
element of the additional data added by T(B).
"""
function partial_map_classifier_universal_property(
    m::CSetTransformation{S}, f::CSetTransformation{S}
    )::CSetTransformation where {S}
  hdata = collect(zip(hom(S),dom(S),codom(S)))

  A, B = codom(m), codom(f)
  ηB = partial_map_classifier_eta(B)
  TB = codom(ηB)
  res = Dict{Symbol, Vector{Int}}()
  for o in ob(S)
    res[o] = Int[]
    homs_cds = [(h,cd) for (h,d,cd) in hdata if d==o]
    codom_data = isempty(homs_cds) ? [] : collect.(
      zip([TB[h] for h in first.(homs_cds)]...))

    for i in parts(A, o)
      xa=findfirst(==(i), collect(m[o]))
      if !isnothing(xa)
        push!(res[o], f[o](xa))
      elseif isempty(codom_data)
        # There is no outgoing morphism data to match up, so send to the +1 elem
        push!(res[o], nparts(B, o)+1)
      else
        # find which args of this element have been deleted
        args = [findfirst(==(A[h][i]), collect(m[cd])) for (h,cd) in homs_cds]
        # Get the outgoing morphism data for this deleted element
        outdata = [isnothing(v) ? nparts(B, cd)+1 : v
                  for ((_,cd),v) in zip(homs_cds, args)]
        # Identify which element of T(o) to send it to based on the out-data.
        for (j, outdata_) in reverse(collect(enumerate(codom_data)))
          if outdata_ == outdata
            push!(res[o], j)
            break
          end
        end
      end
    end
  end
  return CSetTransformation(A, TB; res...)
end

"""
See Theorem 2 of 'Concurrency Theorems for Non-linear Rewriting Theories'
"""
function final_pullback_complement(fm::ComposablePair)::ComposablePair
  f, m = fm
  A, B = dom(f), codom(f)
  m_bar = partial_map_classifier_universal_property(m, id(B))
  T_f = partial_map_functor_hom(f)
  pb_2 = pullback(T_f, m_bar)
  _, g = pb_2.cone
  s = Span(partial_map_classifier_eta(A), compose(f,m))
  n = universal(pb_2, s)
  return ComposablePair(n, g)
end

"""
Sesqui-pushout is just like DPO, except we use a final pullback complement
instead of a pushout complement.
"""
function sesqui_pushout_rewrite_data(
    o::CSetTransformation,
    i::CSetTransformation,
    m::CSetTransformation
    )::Tuple{CSetTransformation,CSetTransformation,
             CSetTransformation,CSetTransformation}
  m_, i_ = final_pullback_complement(ComposablePair(i, m))
  m__, o_ = pushout(o, m_).cocone

  return (m__, o_, m_, i_)
end

"""Just get the result of the SqPO transformation"""
function sesqui_pushout_rewrite(
    o::CSetTransformation, i::CSetTransformation, m::CSetTransformation
    )::StructCSet
  m__, _, _, _ = sesqui_pushout_rewrite_data(o,i,m)
  return codom(m__)
end

end
