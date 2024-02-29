module CatlabNautyExt

using nauty_jll
import Catlab.CategoricalAlgebra.CSets: ACSetTransformation, Multispan, 
  Multicospan, apex, legs
using Catlab.Theories: ⋅
using ACSets
import ACSets: call_nauty, strhsh, orbits, ngroup, canon, dom, codom
using StructEquality

# Morphisms up to isomorphism
#----------------------------

"""
Given an ACSet X and a canonical element of the iso class, [X], obtain either
a map X -> [X] or (if `inv=true`) [X]->X
"""
function ACSetTransformation(start::ACSet, n::CSetNautyRes; inv::Bool=false) 
  comps = Dict([k => (inv ? invperm(v) : v) for (k, v) in pairs(canonmap(n))])
  args = (inv ? reverse : identity)([start, canon(n)])
  ACSetTransformation(args...; comps...)
end

"""
Given an ACSetTransformation A -> B (and canonical isos A→A' and B→B′), we 
construct a canonical ACSetTransformation A′→B′.
"""
@struct_hash_equal struct ACSetTransformationNautyRes <: NautyRes 
  dom::CSetNautyRes
  codom::CSetNautyRes
  canon::ACSetTransformation # Cache the computation of this
end

"""Optionally pass in the CSetNautyRes for (co)dom if known"""
function call_nauty(f::ACSetTransformation; dom_canon=nothing, codom_canon=nothing) 
  d, cd = map([dom=>dom_canon, codom=>codom_canon]) do (get, canon)
    isnothing(canon) ? call_nauty(get(f)) : canon
  end
  d′ = ACSetTransformation(dom(f), d; inv=true)
  cd′ = ACSetTransformation(codom(f), cd)
  ACSetTransformationNautyRes(d, cd, d′⋅f⋅cd′)
end

dom(n::ACSetTransformationNautyRes) = n.dom
codom(n::ACSetTransformationNautyRes) = n.codom

strhsh(n::ACSetTransformationNautyRes) = strhsh(n.dom) * strhsh(n.codom) 
orbits(n::ACSetTransformationNautyRes) = orbits(dom(n)) => orbits(codom(n))
generators(n::ACSetTransformationNautyRes) = generators(dom(n)) => generators(codom(n))
ngroup(n::ACSetTransformationNautyRes) = ngroup(dom(n)) => ngroup(codom(n))
canon(n::ACSetTransformationNautyRes) = n.canon

# (Co)spans up to isomorphism
#----------------------------

abstract type SpanCospanNautyRes <: NautyRes end

@struct_hash_equal struct MultispanNautyRes <: SpanCospanNautyRes 
  apex::CSetNautyRes
  legs::AbstractVector{ACSetTransformationNautyRes}
end

@struct_hash_equal struct MulticospanNautyRes <: SpanCospanNautyRes 
  apex::CSetNautyRes
  legs::AbstractVector{ACSetTransformationNautyRes}
end

apex(s::SpanCospanNautyRes) = s.apex
legs(s::SpanCospanNautyRes) = s.legs
Base.length(s::SpanCospanNautyRes) = length(s.legs)

function call_nauty(f::Multispan)
  ap = call_nauty(apex(f))
  MultispanNautyRes(ap, call_nauty.(f; dom_canon=ap))
end

function call_nauty(f::Multicospan)
  ap = call_nauty(apex(f))
  MulticospanNautyRes(ap, call_nauty.(f; codom_canon=ap))
end


strhsh(n::SpanCospanNautyRes) = join(strhsh.(legs(n)))
orbits(n::SpanCospanNautyRes) = [orbits(apex(n)), orbits.(codom.(legs(n)))...]
generators(n::SpanCospanNautyRes) = [generators(apex(n)), generators.(codom.(legs(n)))...]
ngroup(n::SpanCospanNautyRes) = [ngroup(apex(n)), ngroup.(codom.(legs(n)))...]
canon(n::SpanCospanNautyRes) = Multispan(canon.(legs(n)))

# C-Set diagrams up to isomorphism - TODO
#----------------------------------------

end # module
