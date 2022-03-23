module Chase
export ED, chase, chase_step, active_triggers, morphism_constraint

using ...Theories
using ..CSets
using ..Limits
import ...Theories: dom, codom

"""
A morphism S->T, encoding an embedded dependency. If the pattern S is matched
(via a homomorphism S->I), we demand there exist a morphism T->I that makes the
triangle commute.
"""
struct ED
  ST :: ACSetTransformation
end

dom(e::ED) = dom(e.ST)
codom(e::ED) = codom(e.ST)


VPSI = Vector{Pair{Symbol,Int}}
"""
Chase a CSet instance (attributes are tricky - TODO) given a list of embedded
dependencies. This may not terminate, so a bound on the number of iterations is
required.

Σ S  ⟶ Iₙ
 ↓      ⋮
Σ T ... Iₙ₊₁

There is a copy of S and T for each active trigger. A trigger is a map from S
into the current instance. What makes it 'active' is that there is no morphism
from T to I that makes the triangle commute.

Each iteration constructs this pushout square. This is used to maintain the
identity of which elements are inputs/outputs when considering CSet instances
as open hypergraphs.
"""
function chase(Iio::Tuple{T_,VPSI,VPSI}, Σ::Vector{ED}, n::Int;
  verbose=false)::Tuple{T_,VPSI,VPSI} where T_<:StructACSet
  Iio = deepcopy(Iio)     # do not modify the input acset
  for i in 1:n
    if verbose println("Iter $i") end
    Iio = chase_step(Iio, Σ)
  end
  return Iio
end

function chase(I::T, Σ::Vector{ED}, n::Int; verbose=false
               )::Tuple{T,VPSI,VPSI} where T<:StructACSet
  chase((I, Pair{Symbol,Int}[], Pair{Symbol,Int}[]), Σ, n; verbose=verbose)
end

"""
Naively determine active triggers of EDs (S->T) by filtering all triggers
(i.e. maps S->I) to see which are active (i.e. there exists no T->I such that
S->T->I = S->I).

Optionally restrict to only considering a subset of the triggers with `ts`, a
list of indices into the list of triggers.
"""
function active_triggers(I::T_, Σ::Vector{ED}; ts::Vector{Int}=Int[]
                  )::Vector{Pair{ACSetTransformation, ACSetTransformation}} where {
                    T_<:StructACSet}
  maps = Pair{ACSetTransformation, ACSetTransformation}[]
  for ed_ in Σ
    ed, S, T = ed_.ST, dom(ed_), codom(ed_) # unpack embedded dependency info
    for trigger in last.(filter(ih->isempty(ts) || ih[1] in ts,
                                collect(enumerate(homomorphisms(S, I)))))
      constr = morphism_constraint(ed, trigger) # commutative triangle constr
      if isnothing(constr) || !is_homomorphic(T, I, initial=constr)
        push!(maps, trigger => ed)
      end
    end
  end
  return maps
end

"""
Run a single chase step. Optionally select a subset of triggers to fire on.
This selection could be generalized to be a function which does a computation
to determine which firings are useful.
"""
function chase_step(Iio::Tuple{T_,VPSI,VPSI}, Σ::Vector{ED};
                    ts::Vector{Int}=Int[]
                   )::Tuple{T_,VPSI,VPSI} where T_<:StructACSet
    I, ins, outs = Iio
    ats = active_triggers(I, Σ; ts=ts)
    if isempty(ats)  # Early termination condition
      return I, ins, outs
    end
    r_i_maps, r_s_maps = first.(ats), last.(ats)
    # Combine each list of morphisms into a single one & take pushout
    I_po = pushout(copairs(r_i_maps, true), copairs(r_s_maps, false))
    # Propagate info about which vertices are inputs/outputs & update I
    ins, outs = [[k=>legs(I_po)[1][k](v) for (k,v) in x] for x in [ins, outs]]
    return apex(I_po), ins, outs
end


"""
A span T<-S->I partially determines a map T->I if we wish to produce a
commutative triangle. This generates the constraints for the homomorphism
finding algorithm when looking for T->I.

It's possible these constraints cannot be satisfied, when s₁,s₂ ∈ S map to
distinct elements in I but to the same element in T. Return `nothing` in this
case, which is interpreted as signaling that the trigger must be active.
"""
function morphism_constraint(S_T::ACSetTransformation{T},
                             S_I::ACSetTransformation{T}
                             )::Union{Nothing,NamedTuple} where T
  d = Dict{Symbol,Dict{Int,Int}}()
  for (sym, s_t) in pairs(S_T.components)
    t_i, s_i = Dict{Int,Int}(), S_I[sym]
    for (t, i) in zip(collect(s_t), collect(s_i))
      if haskey(t_i, t) && (i != t_i[t])
        return nothing # unsat
      end
      t_i[t] = i
    end
    d[sym] = t_i
  end
  return NamedTuple(d)
end

"""
Construct Σᵢ hᵢ: Aᵢ->Bᵢ to get a morphism from ΣᵢAᵢ -> ΣᵢBᵢ
If all Bᵢ are the same, then we can get a morphism ΣᵢAᵢ -> B with `shared_tgt`
"""
function copairs(xs::Vector{T}, shared_tgt::Bool
                 )::ACSetTransformation where T<:ACSetTransformation
  comps = Dict([k=>Int[] for k in keys(xs[1].components)])
  new_d = Base.invokelatest(typeof(dom(xs[1])))
  new_cd = shared_tgt ? codom(xs[1]) : Base.invokelatest(typeof(codom(xs[1])))
  for x in xs
    copy_parts!(new_d,dom(x))
    if shared_tgt
      for k in keys(x.components) append!(comps[k], collect(x[k])) end
    else
      for (k,v) in pairs(copy_parts!(new_cd,codom(x)))
        append!(comps[k], [v.start + vv - 1 for vv in collect(x[k])])
      end
    end
  end
  return ACSetTransformation(new_d, new_cd; comps...)
end

end # module