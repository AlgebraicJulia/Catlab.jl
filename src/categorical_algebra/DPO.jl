module DPO
export rewrite, rewrite_match, valid_dpo, dangling_condition, id_condition, pushout_complement

using ..FinSets
using ..CSets
using ..Limits
using ...Theories
using ...Theories: attr


"""
    l
  L ← I
m ↓   ↓k
  G ← K
    g

Compute a pushout complement, componentwise in Set. On a formal level:
For each component, define K = G / m(L/l(I)). There is a natural injection g: K↪G
For each component, define k as equal to the map l;m (every element in the image in G is also in K).

Returns ACSetTransformations k and g such that (m, g) is the pushout of (l, k)

Implementation-wise, elements of K are ordered in the same order as they appear in G.
Construct an offset mapping to keep track of the location of elements of G within K.
"""
function pushout_complement(l::ACSetTransformation{CD,AD},m::ACSetTransformation{CD,AD})::Pair{ACSetTransformation{CD,AD},ACSetTransformation{CD,AD}} where {CD,AD}
  @assert valid_dpo(l, m; fail=true)

  I, L, G = dom(l), codom(l), codom(m)
  lm = compose(l, m)

  k_components = Dict{Symbol, FinFunction}()
  g_components = Dict{Symbol,Vector{Int}}()
  K = ACSet{typeof(G).parameters...}()
  offsets = Dict{Symbol,Vector{Int}}()


  for comp in keys(l.components)

    n_comp = nparts(G, comp)  # total # of elements in G
    l_image = Set(l.components[comp].func)

    # m(L/l(G)): image of (complement of image of l) into G
    orphans = sort(map(x->m[comp](x),
                  filter(x->!(x in l_image),
                      1:nparts(L,comp))))
    orph_set = Set(orphans)  # for membership test

    # Compute map from G to K (undefined for orphans)
    offsets[comp] = reindex(n_comp, orphans)

    # Natural injection of subset of G into G
    g_components[comp] = filter(x->!(x in orph_set), 1:n_comp)

    # Initialize component in K
    add_parts!(K, comp, length(g_components[comp]))

    # Adjust lg function from I→G to refer to K using the offset
    newFunc = [x - offsets[comp][x] for x in lm.components[comp].func]
    k_components[comp] = FinFunction(newFunc, n_comp - length(orphans))
  end

  # Populate attributes for K (unchanged from G)
  for (i, attr) in enumerate(attr(AD))
    new=[G[attr][j] for j in g_components[dom(AD,i)]]
    set_subpart!(K, attr, new)
  end

  # Populate relations for K (same as G, with offset applied)
  for (i, col) in enumerate(hom(CD))
    src_, tgt_ = dom(CD,i), codom(CD,i)
    new=[val - offsets[tgt_][val] for val in G[col][g_components[src_]]]
    set_subpart!(K, col, new)
  end

  # Put together all information into new morphisms
  k = ACSetTransformation(I, K; k_components...)
  g = ACSetTransformation(K, G; g_components...)

  return k => g
end

"""
Compute offsets induced by removing particular elements from
the list 1:n. E.g. if we remove elements 2 and 4 from 1:5,
our offset is [0,_,1,_,2]
(the offset at the removed element index is not meaningful)
"""
function reindex(n::Int, removed::Vector{Int})::Vector{Int}
  offset, off_counter, o_index = [],0,1
  for i in 1:n
    while o_index <= length(removed) && removed[o_index] < i
      if removed[o_index] < i
        off_counter +=1
      end
      o_index += 1
    end
    push!(offset, off_counter)
  end
  return offset
end

"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite.
"""
function rewrite_match(L::ACSetTransformation{CD, AD},
                       R::ACSetTransformation{CD, AD},
                       m::ACSetTransformation{CD, AD}
                      )::AbstractACSet{CD, AD} where {CD, AD}
    @assert dom(L) == dom(R)
    @assert L.codom == dom(m)
    (k, _) = pushout_complement(L, m)
    l1, _ = pushout(R, k)
    return l1.codom
end

"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet,
where a match morphism is found automatically. If multiple
matches are found, a particular one can be selected using
`m_index`.
"""
function rewrite(L::ACSetTransformation{CD, AD},
                 R::ACSetTransformation{CD, AD},
                 G::AbstractACSet{CD, AD},
                 monic::Bool=false,
                 m_index::Int=1
                )::Union{Nothing, AbstractACSet} where {CD, AD}
  ms = filter(m->valid_dpo(L, m), homomorphisms(L.codom, G, monic=monic))
  if 0 < m_index <= length(ms)
    return rewrite_match(L, R, ms[m_index])
  else
    return nothing
  end
end


"""
Condition for existence of a pushout complement
"""
function valid_dpo(L::ACSetTransformation, m::ACSetTransformation; fail::Bool=false)::Bool
  return id_condition(L, m;fail=fail) && dangling_condition(L, m;fail=fail)
end

"""
Does not map both a deleted item and a preserved item in L to the same item in G, or two distinct deleted items to the same.
(Trivially satisfied if match is mono)
"""
function id_condition(L::ACSetTransformation{CD, AD},
                      m::ACSetTransformation{CD, AD};
                      fail::Bool=false
                     )::Bool where {CD, AD}
  for comp in keys(L.components)
    m_comp = x->m[comp](x)
    image = Set(L.components[comp].func)
    image_complement = filter(x->!(x in image), 1:nparts(L.codom,comp))
    image_vals = map(m_comp, collect(image))
    orphan_vals = map(m_comp, image_complement)
    orphan_set = Set(orphan_vals)
    if length(orphan_set)!=length(orphan_vals)
      if fail
        for (i, iv) in enumerate(image_complement)
          for j in i+1:length(image_complement)
            if m_comp(iv) == m_comp(image_complement[j])
              @assert false ("$comp #$i+$j both orphaned and sent to $(m_comp(i))")
            end
          end
        end
      end
      return false
    end
    if !isempty(intersect(image_vals, orphan_set))
      if fail
        for i in image
          if m_comp(i) in orphan_set
            @assert false ("Nondeleted $comp #$i in L mapped to deleted val $(m_comp(i)) in G")
          end
        end
      end
      return false
    end
  end

  return true
end

"""
Dangling condition:
m doesn't map a deleted element d to a element m(d) ∈ G if m(d) is connected to something outside the image of m.
For example, in the CSet of graphs:
  e1
1 --> 2   --- if e1 is not matched but either 1 and 2 are deleted, then e1 is dangling
"""
function dangling_condition(L::ACSetTransformation{CD, AD},
                            m::ACSetTransformation{CD, AD};
                            fail::Bool=false
                           )::Bool where {CD, AD}
  orphans = Dict()
  for comp in keys(L.components)
    image = Set(L.components[comp].func)
    orphans[comp] = Set(
      map(x->m[comp](x),
        filter(x->!(x in image),
          1:nparts(codom(L),comp))))
  end
  # check that for all morphisms in C, we do not map to an orphan
  for (morph, src_ind, tgt_ind) in zip(hom(CD), dom(CD), codom(CD))
    src_obj = ob(CD)[src_ind] # e.g. :E, given morph=:src in graphs
    tgt_obj = ob(CD)[tgt_ind] # e.g. :V, given morph=:src in graphs
    n_src = 1:nparts(codom(m),src_obj)
    unmatched_vals = setdiff(n_src, m[src_obj].func)
    unmatched_tgt = map(x -> m.codom[morph][x], collect(unmatched_vals))
    if !isempty(intersect(unmatched_tgt, orphans[tgt_obj]))
      if fail
        for unmatched_val in setdiff(n_src, m[src_obj].func)  # G/m(L) src
          unmatched_tgt = m.codom[morph][unmatched_val]
          if codom(m)[morph][unmatched_val] in orphans[tgt_obj]
              @assert false ("Dangling condition violation: $src_obj#$unmatched_val --$morph--> $tgt_obj#$unmatched_tgt")
          end
        end
      end
      return false
    end
  end
  return true
end

end
