module DPO
export Rule, rewrite, rewrite_match, rewrite_parallel, rewrite_maps,
       rewrite_match_maps, rewrite_parallel_maps, rewrite_dpo, rewrite_spo,
       rewrite_sqpo, extend_morphism

using ...Theories, ...Present, ...Graphs
using ..FinSets, ..CSets, ..FreeDiagrams, ..Limits
using ..FinSets: id_condition
using ..CSets: dangling_condition, ¬
using DataStructures
using AutoHashEquals

# Generic rewriting tooling
###########################
"""
Rewrite rules are encoded as spans. The L morphism encodes a pattern to be
matched. The R morphism encodes a replacement pattern to be substituted in.

A semantics (DPO, SPO, or SqPO) must be chosen.

Control the match-finding process by specifying whether the match is
intended to be monic or not, as well as an optional negative application
condition(s) (i.e. forbid any match m: L->G for which there exists a commuting
triangle L->Nᵢ->G, for each Nᵢ).
"""
struct Rule{T}
  L::Any
  R::Any
  N::Vector{Any}
  monic::Bool
  function Rule{T}(L, R, N=nothing; monic::Bool=false) where {T}
    dom(L) == dom(R) || error("L<->R not a span")
    Ns = isnothing(N) ? [] : (N isa ACSetTransformation ? Any[N] : N)
    all(N-> dom(N) == codom(L), Ns) || error("NAC does not compose with L")
    new{T}(L, R, Ns, monic)
  end
end

Rule(L,R,N=nothing;monic::Bool=false) = Rule{:DPO}(L,R,N; monic=monic)

# Rewriting functions that just get the final result
"""    rewrite(r::Rule, G; kw...)
Perform a rewrite (automatically finding an arbitrary match) and return result.
"""
rewrite(r::Rule{T}, G; kw...) where {T} =
  get_result(T, rewrite_maps(r, G; kw...))

"""    rewrite_match(r::Rule, m; kw...)
Perform a rewrite (with a supplied match morphism) and return result.
"""
rewrite_match(r::Rule{T}, m; kw...) where {T} =
  get_result(T, rewrite_match_maps(r, m; kw...))

"""    rewrite_parallel(rs::Vector{Rule}, G; kw...)
Perform multiple rewrites in parallel (automatically finding arbitrary matches)
and return result.
"""
rewrite_parallel(rs::Vector{Rule{T}}, G; kw...) where {T} =
  get_result(T, rewrite_parallel_maps(rs, G; kw...))
rewrite_parallel(r::Rule, G; kw...) = rewrite_parallel([r], G; kw...)

"""Extract the rewrite result from the full output data"""
function get_result(sem::Symbol, maps)
  if isnothing(maps)  nothing
  elseif sem == :DPO  codom(maps[4])
  elseif sem == :SPO  codom(maps[8])
  elseif sem == :SqPO codom(maps[1])
  else   error("Rewriting semantics $sem not supported")
  end
end


"""    rewrite_maps(r::Rule, G; initial=Dict(), kw...)
Perform a rewrite (automatically finding an arbitrary match) and return all
computed data.
"""
function rewrite_maps(r::Rule{T}, G; initial=Dict(), kw...) where {T}
  ms = homomorphisms(codom(r.L), G; monic=r.monic, initial=NamedTuple(initial))
  for m in ms
    DPO_pass = T != :DPO || can_pushout_complement(r.L, m)
    if DPO_pass && all(N->isnothing(extend_morphism(m,r.N)), r.N)
      return rewrite_match_maps(r, m; kw...)
    end
  end
  return nothing
end


"""    rewrite_parallel_maps(rs::Vector{Rule{T}}, G::StructACSet{S}; initial=Dict(), kw...) where {S,T}
Perform multiple rewrites in parallel (automatically finding arbitrary matches)
and return all computed data. Restricted to C-set rewriting
"""
function rewrite_parallel_maps(rs::Vector{Rule{T}}, G::StructACSet{S};
                               initial=Dict(), kw...) where {S,T}
  (ms,Ls,Rs) = [ACSetTransformation{S}[] for _ in 1:3]
  seen = [Set{Int}() for _ in ob(S)]
  init = NamedTuple(initial)
  for r in rs
    ms_ = homomorphisms(codom(r.L), G; monic=r.monic, initial=init)
    for m in ms_
      DPO_pass = T != :DPO || can_pushout_complement(r.L, m)
      if DPO_pass && all(N->isnothing(extend_morphism(m,N)), r.N)
        new_dels = map(zip(components(r.L), components(m))) do (l_comp, m_comp)
            L_image = Set(collect(l_comp))
            del = Set([m_comp(x) for x in codom(l_comp) if x ∉ L_image])
            LM_image = Set(m_comp(collect(L_image)))
            return del => LM_image
        end
        if all(isempty.([x∩new_keep for (x,(_, new_keep)) in zip(seen, new_dels)]))
          for (x, (new_del, new_keep)) in zip(seen, new_dels)
            union!(x, union(new_del, new_keep))
          end
          push!(ms, m); push!(Ls, deepcopy(r.L)); push!(Rs, r.R)
        end
      end
    end
  end
  if isempty(ms) return nothing end
  length(Ls) == length(ms) || error("Ls $Ls")
  # Composite rewrite rule
  R = Rule{T}(oplus(Ls), oplus(Rs))
  return rewrite_match_maps(R, copair(ms); kw...)
end
rewrite_parallel_maps(r::Rule, G; initial=Dict(), kw...) =
  rewrite_parallel_maps([r], G; initial=initial, kw...)


"""    extend_morphism(f::ACSetTransformation,g::ACSetTransformation,monic=false)::Union{Nothing, ACSetTransformation}

Given a span of morphisms, we seek to find a morphism B → C that makes a
commuting triangle if possible.

    B
 g ↗ ↘ ?
 A ⟶ C
   f
"""
function extend_morphism(f::ACSetTransformation, g::ACSetTransformation;
                         monic=false)::Union{Nothing, ACSetTransformation}
  dom(f) == dom(g) || error("f and g are not a span: $jf \n$jg")

  init = Dict{Symbol, Dict{Int,Int}}()
  for (ob, mapping) in pairs(components(f))
    init_comp = Pair{Int,Int}[]
    for i in parts(codom(g), ob)
      vs = Set(mapping(preimage(g[ob], i)))
      if length(vs) == 1
        push!(init_comp, i => only(vs))
      elseif length(vs) > 1 # no homomorphism possible
        return nothing
      end
    end
    init[ob] = Dict(init_comp)
  end
  homomorphism(codom(g), codom(f); initial=NamedTuple(init), monic=monic)
end


# Double-pushout rewriting
##########################

"""    rewrite_match_maps(r::Rule{:DPO}, m)
Apply a DPO rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite.
              l   r
           L <- I -> R
         m ↓    ↓    ↓
           G <- K -> H

This works for any type that implements `pushout_complement` and `pushout`

Returns the morphisms I->K, K->G (produced by pushout complement), followed by
R->H, and K->H (produced by pushout)
"""
function rewrite_match_maps(r::Rule{:DPO}, m; check::Bool=false)
  if check
    can_pushout_complement(r.L, m) || error("Cannot pushout complement $r\n$m")
  end
  (ik, kg) = pushout_complement(r.L, m)
  rh, kh = pushout(r.R, ik)
  return ik, kg, rh, kh
end


# Sesqui-pushout rewriting
##########################

"""
The specification for the following functions comes from:
  - 'Concurrency Theorems for Non-linear Rewriting Theories'
     - for final pullback complement and sesqui-pushout rewriting
  - 'AGREE - Algebraic Graph Rewriting with Controlled Embedding'
     - for partial map classifier (a functor T and natural transformation η)

This implementation is specialized to rewriting CSets
"""

"""Get topological sort of objects of a schema. Fail if cyclic"""
function topo_obs(S::Type)::Vector{Symbol}
  G = Graph(length(ob(S)))
  for (s, t) in zip(S.parameters[5], S.parameters[6])
    add_edge!(G, s, t)
  end
  return [ob(S)[i] for i in reverse(topological_sort(G))]
end

"""Confirm a C-Set satisfies its equational axioms"""
function check_eqs(x::StructACSet, pres::Presentation, o::Symbol, i::Int)::Bool
  for (p1,p2) in filter(e->only(e[1].type_args[1].args) == o, pres.equations)
    eval_path(x, p1, i) == eval_path(x,p2, i) || return false
  end
  return true
end

function eval_path(x::StructACSet, h, i::Int)::Int
  val = i
  for e in h.args
    val = x[val, e]
  end
  return val
end

"""
A functor T, playing the role of Maybe in Set, but generalized to C-Sets.

When called on the terminal object, this produces the subobject classifier:
See Mulry "Partial map classifiers and cartesian closed categories" (1994)

This function specifies what T does on objects. The key properties:
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

In general, T(X) ≅ |X| + ∏ₕ(|T(codom(h))|) for each outgoing morphism h::X⟶Y
- the |X| corresponds to the 'real' elements of X
- the second term corresponds to the possible ways an X can be deleted.
- This recursive formula means we require the schema of the C-set to be acyclic
  otherwise the size is infinite (assumes schema is free).
"""
function partial_map_functor_ob(x::StructCSet{S};
    pres::Union{Nothing, Presentation}=nothing
    )::Pair{StructCSet, Dict{Symbol,Dict{Vector{Int},Int}}} where {S}
  res = deepcopy(x)

  # dict which identifies added elements (of some part o) by the values of its
  # foreign keys
  d = DefaultDict{Symbol,Dict{Vector{Int},Int}}(()->Dict{Vector{Int},Int}())

  hdata = collect(zip(hom(S), dom(S), codom(S)))
  for o in topo_obs(S)
    homs_cds = [(h,cd) for (h,d,cd) in hdata if d==o] # outgoing morphism data
    if isempty(homs_cds)
      d[o][Int[]] = add_part!(res, o)
    else
      homs, cds = collect.(zip(homs_cds...))
      for c in Iterators.product([1:nparts(res,cd) for cd in cds]...)
        d[o][collect(c)] = v = add_part!(res, o; Dict(zip(homs,c))...)

        # Forbid modifications which violate schema equations
        if !isnothing(pres) && !check_eqs(res, pres, o, v)
          delete!(d[o], collect(c))
          rem_part!(res, o, v)
        end
      end
    end
  end
  return res => d
end

"""
Because the functorial embedding of objects keeps a copy of the original data,
what to do with morphisms is just carry them along. Because our implementation
adds all of the additional stuff afterwards, index-wise, we can use literally
the same data for a morphism lifted from X⟶Y to T(X)⟶T(Y).

However, we still need to map the extra stuff in T(X) to the proper extra stuff
in T(Y).
"""
function partial_map_functor_hom(f::CSetTransformation{S};
    pres::Union{Nothing, Presentation}=nothing)::CSetTransformation where S
  X, Y = dom(f), codom(f)
  (d, _), (cd, cddict) = [partial_map_functor_ob(x; pres=pres) for x in [X,Y]]
  comps, mapping = Dict{Symbol,Vector{Int}}(), Dict()
  hdata = collect(zip(hom(S),dom(S),codom(S)))

  for (k,v) in pairs(f.components)
    mapping[k] = vcat(collect(v), [nparts(Y, k)+1]) # map extra val to extra
  end

  for o in topo_obs(S)
    comps[o] = map(parts(d, o)) do i
      if i <= nparts(X,o) # use f for elements that are defined
        return f[o](i)
      else  # find which extra elem ∈ T(Y) it maps to (by its outgoing maps)
        outdata = Int[comps[cd][d[i, h]] for (h,c_,cd) in hdata if c_==o]
        return cddict[o][outdata]
      end
    end
  end
  return CSetTransformation(d,cd;comps...)
end

"""
The natural injection from X ⟶ T(X)
When evaluated on the terminal object, this gives the subobject classfier.
"""
function partial_map_classifier_eta(x::StructCSet{S};
    pres::Union{Nothing, Presentation}=nothing)::CSetTransformation where {S}
  codom = partial_map_functor_ob(x; pres=pres)[1]
  d = Dict([k=>collect(v) for (k,v) in pairs(id(x).components)])
  return CSetTransformation(x, codom; d...)
end



"""A partial function is defined by the following span:
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
    m::CSetTransformation{S}, f::CSetTransformation{S};
    pres::Union{Nothing, Presentation}=nothing, check=false
    )::CSetTransformation where {S}
  hdata   = collect(zip(hom(S),dom(S),codom(S)))
  A, B    = codom(m), codom(f)
  ηB      = partial_map_classifier_eta(B;pres=pres)
  Bdict   = partial_map_functor_ob(B; pres=pres)[2]
  TB      = codom(ηB)
  fdata   = DefaultDict{Symbol, Dict{Int,Int}}(()->Dict{Int,Int}())
  res     = Dict{Symbol, Vector{Int}}()
  unknown = Dict{Symbol, Int}()
  is_injective(m) || error("partial map classifier called w/ non monic m $m")
  # Get mapping of the known values
  for (o, fcomp) in pairs(components(f))
    unknown[o] = nparts(TB, o)
    for (aval, fval) in zip(collect(m[o]), collect(fcomp))
      fdata[o][aval] = fval
    end
  end
  # Compute components of phi
  for o in topo_obs(S)
    res[o] = map(parts(A, o)) do i
      if haskey(fdata[o], i)
        return fdata[o][i]
      else # What kind of unknown value is it?
        homdata = [res[cd][A[i, h]] for (h,d,cd) in hdata if d == o]
        return Bdict[o][homdata]
      end
    end
  end
  ϕ = CSetTransformation(A, TB; res...)
  if check
    is_natural(ηB) || error("ηB not natural $ηB")
    is_natural(ϕ) || error("ϕ not natural $ϕ")
    is_isomorphic(apex(pullback(ηB,ϕ)), dom(m)) || error("Pullback incorrect")
  end
  return ϕ
end

"""
See Theorem 2 of 'Concurrency Theorems for Non-linear Rewriting Theories'
      f
  B <--- A
m ↓      ↓ n
  C <--  D
     g

"""
function final_pullback_complement(fm::ComposablePair;
    pres::Union{Nothing, Presentation}=nothing, check=false)::ComposablePair
  f, m = fm
  A, B = dom(f), codom(f)
  m_bar = partial_map_classifier_universal_property(m, id(B); pres=pres)
  T_f = partial_map_functor_hom(f; pres=pres)
  pb_2 = pullback(T_f, m_bar)
  _, g = pb_2.cone
  s = Span(partial_map_classifier_eta(A; pres=pres), compose(f,m))
  n = universal(pb_2, s)
  !check || is_isomorphic(apex(pullback(m,g)), A) || error("incorrect")
  return ComposablePair(n, g)
end

"""    rewrite_match_maps(r::Rule{:SqPO},m; pres::Union{Nothing, Presentation}=nothing)
Sesqui-pushout is just like DPO, except we use a final pullback complement
instead of a pushout complement.
"""
function rewrite_match_maps(r::Rule{:SqPO},m; pres::Union{Nothing, Presentation}=nothing)
  m_, i_ = final_pullback_complement(ComposablePair(r.L, m); pres=pres)
  m__, o_ = pushout(r.R, m_)
  return (m__, o_, m_, i_)
end


# Single-pushout rewriting
##########################

"""
f         f
A ↣ B     A ↣ B
    ↓ g   ↓   ↓ g
    C     D ↣ C

Define D to be Im(g) to make it the largest possible subset of C such that we
can get a pullback.
"""
function pullback_complement(f, g)
    A = dom(f)
    d_to_c = hom(¬g(¬f(A)))
    # force square to commute by looking for the index in D making it commute
    ad = Dict(map(collect(pairs(components(compose(f,g))))) do (cmp, fg_as)
      cmp => Vector{Int}(map(collect(fg_as)) do fg_a
        findfirst(==(fg_a), collect(d_to_c[cmp]))
      end)
    end)
    return CSetTransformation(A, dom(d_to_c); ad...) => d_to_c
end

"""    rewrite_match_maps(r::Rule{:SPO}, ac)
NOTE: In the following diagram, a double arrow indicates a monic arrow.

We start with two partial morphisms, construct M by pullback, then N & O by
pullback complement, then finally D by pushout.


A ⇇ K → B         A ⇇ K → B
⇈                 ⇈ ⌟ ⇈ ⌞ ⇈
L          ⭆      L ⇇ M → N
↓                 ↓ ⌞ ↓ ⌜ ↓
C                 C ⇇ O → D

We assume the input A→C is total, whereas A→B may be partial, so it is given
as a monic K↣A and K→B.

Specified in Fig 6 of:
"Graph rewriting in some categories of partial morphisms"
"""
function rewrite_match_maps(r::Rule{:SPO}, ac)
  ka, kb = r.L, r.R
  e = "SPO rule is not a partial morphism. Left leg not monic."
  is_injective(ka) || error(e)

  lc, la = ac, id(dom(ac))
  ml, mk = pullback(la, ka)
  mn, nb = pullback_complement(mk, kb)
  mo, oc = pullback_complement(ml, lc)
  od, nd = pushout(mo, mn)
  return [ml, mk, mn, mo, nb, oc, nd, od]
end


end
