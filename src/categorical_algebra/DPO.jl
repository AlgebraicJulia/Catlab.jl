module DPO
export rewrite, rewrite_match, valid_dpo, dangling_condition, id_condition, pushout_complement, extend_cset,subcset

using ..FinSets
import ..CSets: AbstractACSet, ACSet, ACSetTransformation, components, homomorphism, homomorphisms, unpack_components, pack_components, add_parts!, set_subpart!, is_natural
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
We initialize --k-->K with the composite l.m (so K is initialized as G). The image of the
orphans is deleted from K. Elements of I mapping into K will map to their original location
that m sent them to, and any extra elements in K (not in image of k) will go to the elements
of G that were not in the image of m at all.
These respectively satisfy the equality and inequality requirements of the pushout condition.
As we delete things from G to turn it into K, the map m.l needs to adjust the indices of things
it maps to in order to account for this. When we delete element x, then all y>x get renamed to y-1.
"""
function pushout_complement(L::ACSetTransformation,m::ACSetTransformation)::Pair{ACSetTransformation,ACSetTransformation}

  Lm = compose(L, m)
  new_comps, non_orphans  = Dict{Symbol, FinFunction}(), Dict{Symbol,Vector{Int}}()
  offsets = Dict{Symbol,Vector{Int}}()
  K = ACSet{typeof(m.codom).parameters...}()

  for comp in keys(L.components)

    L_image = Set(L.components[comp].func)
    # image of (complement of image of I into L) into G
    orphans = sort(map(x->m[comp](x),
                  filter(x->!(x in L_image),
                      1:length(L.codom.tables[comp]))))
    orph_set = Set(orphans)

    # Tells us how to map from K into G
    non_orphans[comp] = filter(x->!(x in orph_set), 1:length(m.codom.tables[comp]))

    # Start initializing the rows of tables in K
    add_parts!(K, comp, length(non_orphans[comp]))


    # Modify mapping component
    oldfun = Lm.components[comp]

    newFunc, offset, off_counter, o_index = Int[], Int[], 0, 1

    # re-adjust, find offsets (relies on orphans being sorted)
    for i in 1:oldfun.codom.set
      while o_index <= length(orphans) && orphans[o_index] < i
        if orphans[o_index] < i
          off_counter +=1
        end
        o_index += 1
      end
      push!(offset, off_counter)
    end
    @assert length(oldfun.codom) == length(offset)

    for (i, x) in enumerate(oldfun.func)
        if x in orph_set
          throw(ErrorException("Interface $comp #$i maps to $x which was flagged as an orphan"))
        else
          push!(newFunc, x - offset[x])
        end
    end
    offsets[comp] = offset
    new_comps[comp] = FinFunction(newFunc, oldfun.codom.set - length(orphans))
  end

  # Populate data and attributes for K
  comps, arrows, src, tgt = typeof(m.codom).parameters[1].parameters
  attrs, srcs = typeof(m.codom).parameters[2].parameters[3:4]
  for (i, attr) in enumerate(attrs)
    new=[m.codom[attr][j] for j in non_orphans[comps[srcs[i]]]]
    set_subpart!(K, attr, new)
  end

  for (i, col) in enumerate(arrows)
    src_, tgt_ = comps[src[i]], comps[tgt[i]]
    new=[val - offsets[tgt_][val] for val in m.codom[col][non_orphans[src_]]]
    set_subpart!(K, col, new)
  end

  # Put together all information into new morphisms
  k = ACSetTransformation(L.dom, K; new_comps...)
  @assert is_natural(k)
  g = ACSetTransformation(K, m.codom; non_orphans...)
  @assert is_natural(g)

  return k => g
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
                              1:length(L.codom.tables[comp]))
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
            1:length(L.codom.tables[comp]))))
  end
  # check that for all morphisms in C, we do not map to an orphan
  catdesc = typeof(L.dom).parameters[1]
  comps = catdesc.parameters[1]  # e.g. [:V, :E]
  for (morph, src_ind, tgt_ind) in zip(catdesc.parameters[2], catdesc.parameters[3], catdesc.parameters[4])
    src_obj = comps[src_ind] # e.g. :E, given morph=:src in graphs
    tgt_obj = comps[tgt_ind] # e.g. :V, given morph=:src in graphs
    for non_orph_src_val in setdiff(1:length(m.codom.tables[src_obj]), m[src_obj].func) # non_orphans in G
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



"""
Get the minimal connected component for an ACSet given arbitrary subcollections to include
Return the injection from the sub-ACSet
E.g. for graphs, if the original ACSet is:
  V1<--E1-- V2 --E2--> V3    V4 --E3--> V5
and our initial input is to include V1 and E2,
then an injection will be given from:
  V1  V2--E1-->V3
Helpful! If it doesn't exist somewhere else, maybe should be added
Does this need a bidirectional option? (i.e. V1 present means E1 must be present)
"""
function subcset(acs::ACSet; kw...)::ACSetTransformation
  syms = keys(acs.tables)
  queue = Dict{Symbol, Vector{Int}}([
    sym=>Vector{Int}(unique(get(kw, sym, []))) for sym in syms])
  seen = Dict{Symbol,Set{Int}}([
    sym=>Set{Int}() for sym in syms])
  comps = Dict{Symbol,Vector{Int}}([
    sym=>Int[] for sym in syms])
  allcomps, arrows, _, tgt = typeof(acs).parameters[1].parameters
  arrdict = Dict([arrsym => allcomps[i] for (arrsym, i) in zip(arrows, tgt)])
  while !(all(map(isempty, values(queue))))
    newqueue = Dict{Symbol, Vector{Int}}([sym=>Int[] for sym in syms])
    for (sym, vs) in collect(queue)
      for v in vs
          if !(v in seen[sym])
            push!(seen[sym], v)
            push!(comps[sym], v)
            row = acs.tables[sym][v]
            for (arrow, val) in zip(keys(row), row)
              if haskey(arrdict, arrow)  # if not, it's an attribute
                tgt_sym = arrdict[arrow]
                if !(val in seen[tgt_sym])
                  push!(newqueue[tgt_sym],val)
                end
              end
            end
          end
        end
      end
      queue = newqueue
  end
  new = ACSet{typeof(acs).parameters...}()

  # initialize the rows
  for (k, v) in collect(seen)
    add_parts!(new, k, length(v))
  end

  rename = Dict([sym=>Dict([v=>i for (i,v) in enumerate(comp)])
                 for (sym, comp) in collect(comps)])
  # Fill the columns
  for (k, vs) in collect(comps)
    for col in typeof(acs.tables[k]).parameters[1].names
        oldvals = [acs.tables[k][v][col] for v in vs]
        if haskey(arrdict, col)
          newvals = [rename[arrdict[col]][v] for v in oldvals]
        else
          newvals = oldvals # attr
        end
      set_subpart!(new, col, newvals)
    end
  end

  return ACSetTransformation(new, acs; comps...)
end

"""
Add elements to a cset while keeping track of the old ones with an injection
Helpful! If it doesn't exist somewhere else, maybe should be added
Example:
new_graph = extend_cset(graph, V=(3, Dict()),
                        E=(2, Dict([:src=>[1,2],:tgt=>[3,1]])))
"""
function extend_cset(acs::ACSet;kw...)::ACSetTransformation
  new = deepcopy(acs)
  comps = Dict{Symbol,Any}(kw)
  for (comp, (n, args)) in collect(kw)
    add_parts!(new, comp, n; args...)
  end
  return ACSetTransformation(acs, new; Dict([sym=>collect(1:length(tab)) for (sym, tab) in zip(keys(acs.tables),acs.tables)])...)
end

end
