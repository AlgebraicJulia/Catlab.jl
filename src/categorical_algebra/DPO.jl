module DPO
export rewrite, rewrite_match, valid_dpo, dangling_condition, id_condition, pushout_complement, extend_cset,subcset

using ..FinSets
import ..CSets: AbstractACSet, ACSet, ACSetTransformation, components, homomorphism, homomorphisms, unpack_components, pack_components, add_parts!, nparts, set_subpart!, is_natural
using ...Theories
using ..Limits

"""
   l
L <-- I
|     |
|m    |k
v     v
G <-- K
   g

Given I (interface of patterns), L, G (target CSet to rewrite), m (match), l
Find K (interface of CSets), k, and g such that:
  (L -m-> G <-g- D) is the pushout of (L <-l- I -k-> K)

"Orphans" in L are elements not in the image of l. If the square is to be a pushout, then
K -g-> G must not map to anything that m maps an orphan to.

We initialize --k-->K with the composite l;m (so K is initialized as G). The image of the
orphans is deleted from K. Elements of I mapping into K will map to their original location
that m sent them to, and any extra elements in K (not in image of k) will go to the elements
of G that were not in the image of m at all.

These respectively satisfy the equality and inequality requirements of the pushout condition.
As we delete things from G to turn it into K, the map m;l needs to adjust the indices of things
it maps to in order to account for this. When we delete element x, then all y>x get renamed to y-1.
"""
function pushout_complement(l::ACSetTransformation,m::ACSetTransformation)::Pair{ACSetTransformation,ACSetTransformation}

  I, L, G = l.dom, l.codom, m.codom
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

    # Tells us how to map from K into G
    g_components[comp] = filter(x->!(x in orph_set), 1:n_comp)

    # Start initializing the rows of tables in K
    add_parts!(K, comp, length(g_components[comp]))

    # re-adjust, find offsets (relies on orphans being sorted)
    offsets[comp] = reindex(n_comp, orphans)

    # Define k's action on component in relation to Lm's action
    newFunc = [x - offsets[comp][x] for x in lm.components[comp].func]
    k_components[comp] = FinFunction(newFunc, n_comp - length(orphans))
  end

  # Populate attributes for K (unchanged from G)
  comps, arrows, src, tgt = typeof(G).parameters[1].parameters
  attrs, srcs = typeof(G).parameters[2].parameters[3:4]
  for (i, attr) in enumerate(attrs)
    new=[G[attr][j] for j in g_components[comps[srcs[i]]]]
    set_subpart!(K, attr, new)
  end

  # Populate relations for K (same as G, with offset applied)
  for (i, col) in enumerate(arrows)
    src_, tgt_ = comps[src[i]], comps[tgt[i]]
    new=[val - offsets[tgt_][val] for val in G[col][g_components[src_]]]
    set_subpart!(K, col, new)
  end

  # Put together all information into new morphisms
  k = ACSetTransformation(I, K; k_components...)
  @assert is_natural(k)
  g = ACSetTransformation(K, G; g_components...)
  @assert is_natural(g)

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
Rewrite with explicit match
"""
function rewrite_match(L::ACSetTransformation, R::ACSetTransformation, m::ACSetTransformation)::AbstractACSet
    @assert L.dom == R.dom
    @assert L.codom == m.dom
    @assert valid_dpo(L, m)
    @assert is_natural(L)
    @assert is_natural(R)
    (k, _) = pushout_complement(L, m)
    l1, _ = pushout(R, k).cocone.legs
    return l1.codom
end

"""
Don't explicitly choose the match
"""
function rewrite(L::ACSetTransformation,
                 R::ACSetTransformation,
                 G::AbstractACSet,
                 monic::Bool=false,
                 m_index::Int=1
                 )::Union{Nothing, AbstractACSet}
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
function valid_dpo(L::ACSetTransformation, m::ACSetTransformation, verbose::Bool=false)::Bool
  return id_condition(L, m) && dangling_condition(L, m)
end

"""
Does not map both a deleted item and a preserved item in L to the same item in G, or two distinct deleted items to the same.
(Trivially satisfied if match is mono)
"""
function id_condition(L::ACSetTransformation, m::ACSetTransformation, verbose::Bool=false)::Bool

  for comp in keys(L.components)
    image = Set(L.components[comp].func)
    image_complement = filter(x->!(x in image),
                              1:nparts(L.codom,comp))
    orphan_vals = map(x->m[comp](x), image_complement)
    orphan_set = Set(orphan_vals)
    if length(orphan_set)!=length(orphan_vals)
      if verbose
        for (i, iv) in enumerate(image_complement)
          for j in i+1:length(image_complement)
            if m[comp][i] == m[comp][image_complement[j]]
              println("$comp #$i and $j both orphaned and sent to $(m[comp][i])")
            end
          end
        end
      end
      return false
    end
    for nondel_L in L[comp].func  # for each non-orphan val in G
      if m[comp](nondel_L) in orphan_set
        return false  # non-orphan mapped to same node in G as an orphan
      end
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
function dangling_condition(L::ACSetTransformation, m::ACSetTransformation, verbose::Bool=false)::Bool

  orphans = Dict()
  for comp in keys(L.components)
    image = Set(L.components[comp].func)
      orphans[comp] = Set(
        map(x->m[comp](x),
          filter(x->!(x in image),
            1:nparts(L.codom,comp))))
  end
  # check that for all morphisms in C, we do not map to an orphan
  catdesc = typeof(L.dom).parameters[1]
  comps = catdesc.parameters[1]  # e.g. [:V, :E]
  for (morph, src_ind, tgt_ind) in zip(catdesc.parameters[2], catdesc.parameters[3], catdesc.parameters[4])
    src_obj = comps[src_ind] # e.g. :E, given morph=:src in graphs
    tgt_obj = comps[tgt_ind] # e.g. :V, given morph=:src in graphs
    for non_orph_src_val in setdiff(1:nparts(m.codom,src_obj), m[src_obj].func) # g_components in G
      orphan_tgt_val = m.codom[morph][non_orph_src_val]
      if m.codom[morph][non_orph_src_val] in orphans[tgt_obj]
        if verbose
          println("Dangling condition violation: $src_obj#$non_orph_src_val --$morph--> $tgt_obj#$orphan_tgt_val")
        end
        return false
      end
    end
  end
  return true
end

end
