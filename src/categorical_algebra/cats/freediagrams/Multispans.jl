module Multispans 

export Multispan, Multicospan, Span, Cospan, SMultispan, SMulticospan, apex, feet, legs

using StaticArrays: StaticVector, SVector
using StructEquality, MLStyle
using GATlab 

using .....Theories: dom, codom, ThCategory
using .....BasicSets: FinSet
import .....BasicSets: left, right, untag

using ...FreeDiagrams: ThFreeDiagram, FreeDiagram
import ...FreeDiagrams: fmap, cone_objects, cocone_objects, specialize

using .ThFreeDiagram

#############################################
# Common to (multi)spans and (multi)cospans #
#############################################

abstract type MultiSpanCospan end

Base.getindex(m::MultiSpanCospan, i) = legs(m)[i]

apex(m::MultiSpanCospan) = m.apex
legs(m::MultiSpanCospan) = m.legs
feet(m::MultiSpanCospan) = m.feet

Base.length(m::MultiSpanCospan) = length(legs(m))

Base.iterate(m::MultiSpanCospan, x...) = iterate(legs(m), x...)

function left(s::MultiSpanCospan) 
  length(s) == 2 || error("Span/Cospan does has $(length(s)) legs")
  first(legs(s))
end

function right(s::MultiSpanCospan) 
  length(s) == 2 || error("Span/Cospan does has $(length(s)) legs")
  last(legs(s))
end


##############
# Multispans #
##############
""" Multispan of morphisms in a category.

A [multispan](https://ncatlab.org/nlab/show/multispan) is like a [`Span`](@ref)
except that it may have a number of legs different than two. A colimit of this
shape is a pushout.
"""
@struct_hash_equal struct Multispan{Ob, Hom, Foot, 
    V<:AbstractVector{<:Hom}, W<:AbstractVector{<:Foot}} <: MultiSpanCospan  
  apex::Ob
  legs::V
  feet::W
  function Multispan{O, H, F}(apx::O, legvec::V, feetvec::W
      ) where {O,H,F,V<:AbstractVector{<:H}, W<:AbstractVector{<:F}}
    # Validate
    nf, nl = length(feetvec), length(legvec)
    nf == nl || error("$(nf) feet != $nl legs")
    # Construct
    new{O, H, F, V, W}(apx, legvec, feetvec)
  end
end

const SMultispan{N,Ob,Hom,Foot} = 
  Multispan{Ob,Hom,Foot,<:StaticVector{N,Hom}, <:StaticVector{N,Foot}}

SMultispan{N}(apex, legs::Vararg{Any,N}; cat=nothing) where N =
  Multispan(apex, SVector{N}(legs...); cat)

SMultispan{N}(legs::Vararg{Any,N}; cat=nothing) where N =   
  Multispan(SVector{N}(legs...); cat)

""" Span of morphism in a category.

A common special case of [`Multispan`](@ref). See also [`Cospan`](@ref).
"""
const Span{Ob,Hom,Foot} = SMultispan{2,Ob,Hom,Foot}

Multispan(apex::Ob,legs::AbstractVector{Hom},feet::AbstractVector{Foot}
         ) where {Ob,Hom,Foot} = Multispan{Ob,Hom,Foot}(apex, legs, feet)

""" 
If a `Category` is not provided, we must implicitly assume that the category 
structure comes from type dispatch.
In this setting, we can check upon construction whether or not it is a valid 
span.
"""
function Multispan{Ob,Hom}(apex::Ob,legs::AbstractVector{<:Hom}; cat=nothing
                          ) where {Ob,Hom} 
  𝒞 = isnothing(cat) ? Dispatch(ThCategory, [Ob,Hom]) : cat
  baddoms = [dom[𝒞](l) for l in legs if dom[𝒞](l)!=apex]
  isempty(baddoms) || error("Bad span $baddoms != $apex")
  feet = codom[𝒞].(legs)
  Multispan{Ob,Hom, eltype(feet)}(apex, legs, feet)
end

""" Construct from just a list, assuming it's nonempty """
function Multispan(legs::AbstractVector; cat=nothing) 
  l = first(legs)
  apx = isnothing(cat) ? dom(l) : dom[cat](l)
  Multispan(apx, legs; cat)
end 

""" Cast a span to a Multispan """
Multispan(s::Span{Ob,Hom,Foot}) where {Ob, Hom, Foot} = 
  Multispan{Ob,Hom}(apex(s), legs(s), feet(s))

""" Empty span """
Multispan{Ob, Hom, Foot}(a::Ob) where {Ob, Hom, Foot} = 
  Multispan{Ob, Hom}(a, Hom[], Foot[])


function Multispan{Ob, Hom}(hs::AbstractVector{<:Hom}) where {Ob, Hom} 
  isempty(hs) && error("Multispan needs an apex")   
  allequal(dom.(hs)) || error("Span domains not equal")
  Multispan{Ob, Hom}(dom(first(hs)), hs)
end

function Multispan(apex::Ob,legs::AbstractVector{Hom}; cat=nothing) where {Ob,Hom} 
  Multispan{Ob, Hom}(apex, legs; cat)
end


cocone_objects(span::Multispan) = feet(span)


@instance ThFreeDiagram{Int,Int,Union{Ob,Foot},Hom
                       } [model::Multispan{Ob,Hom,Foot,V,W}
                         ] where {Ob, Hom, Foot, V, W} begin
  src(::Int)::Int = 1
  tgt(x::Int)::Int = x+1
  obmap(x::Int)::Union{Ob,Foot} = @match x begin 
    1 => apex(model)
    i => feet(model)[i-1]
  end
  hommap(i::Int)::Hom = model[i]
  obset()::FinSet = FinSet(length(model)+1)
  homset()::FinSet = FinSet(length(model))
end


""" Specialize a free diagram (can fail) """
function specialize(::Type{Multispan}, d::FreeDiagram)
  es = homset(d)
  apex_v = only(unique(src.(Ref(d), es)))
  feet = obmap.(Ref(d), tgt.(Ref(d), es))
  Multispan(obmap(d, apex_v), hommap.(Ref(d), es), feet)
end


""" Replace homs via a replacement function """
function fmap(d::Multispan, o, h, O::Type, H::Type)
  new_apex::O = o(apex(d))
  new_legs::Vector{H} = h.(legs(d))
  new_feet::Vector{O} = Vector{O}(o.(feet(d)))
  Multispan{O,H,O}(new_apex, new_legs, new_feet)
end

function untag(d::Multispan{Ob,Hom}, i::Int, j::Int) where {Ob,Hom}
  O, H = untag(Ob, i), untag(Hom, j)
  Multispan{O, H, O}(untag(d.apex, i), (x->untag(x, j)).(d.legs), (x->untag(x,i)).(d.feet))
end 

################
# Multicospans #
################

@struct_hash_equal struct Multicospan{Ob, Hom, Feet, 
      V<:AbstractVector{Hom}, U<:AbstractVector{Feet}} <: MultiSpanCospan
  apex::Ob
  legs::V
  feet::U
  function Multicospan{Ob, Hom, Feet}(apex::Ob,legs::V, feet::U
      ) where {Ob,Hom,Feet, V<:AbstractVector{Hom}, U<:AbstractVector{Feet}}
    # Validate
    nf, nl = length(feet), length(legs)
    nf == nl || error("$(nf) feet != $nl legs")

    # Construct
    new{Ob, Hom, Feet, V, U}(apex, legs, feet)
  end
end

const SMulticospan{N,Ob,Hom,Feet} = 
  Multicospan{Ob,Hom,Feet,<:StaticVector{N,Hom}, <:StaticVector{N,Feet}}

SMulticospan{N}(apex, legs::Vararg{Any,N}; cat=nothing) where N =
  Multicospan(apex, SVector{N}(legs...); cat)

SMulticospan{N}(legs::Vararg{Any,N}; cat=nothing) where N = 
  Multicospan(SVector{N}(legs...); cat)

""" Cospan of morphisms in a category.

A common special case of [`Multicospan`](@ref). See also [`Span`](@ref).
"""
const Cospan{Ob,Hom,Foot} = SMulticospan{2,Ob,Hom,Foot}

Multicospan(apex::Ob,legs::AbstractVector{Hom},feet::AbstractVector{Foot}
           ) where {Ob,Hom,Foot} = Multicospan{Ob,Hom,Foot}(apex, legs, feet)

Multicospan(apex::Ob,legs::AbstractVector{Hom}; cat=nothing) where {Ob,Hom} =
  Multicospan{Ob,Hom}(apex, legs; cat)

""" 
Assume that the category this span lives in has `codom` given by type dispatch. 
In this setting, we can check whether or not this is a valid cospan. 
"""
function Multicospan{Ob,Hom}(apex::Ob,legs::AbstractVector{<:Hom}; cat=nothing) where {Ob,Hom} 
  𝒞 = WithModel(isnothing(cat) ? Dispatch(ThCategory, [Ob,Hom]) : cat)
  badcods = [codom(𝒞,l) for l in legs if codom(𝒞,l) != apex]
  isempty(badcods) || error("Bad cospan $badcods != $apex")
  feet = map(legs) do l 
    dom(𝒞,l)
  end
  Multicospan{Ob,Hom, eltype(feet)}(apex, legs, feet)
end

""" Construct from just a list, assuming it's nonempty """
function Multicospan(legs::AbstractVector; cat=nothing)
  l = first(legs)
  apx = isnothing(cat) ? codom(l) : codom[cat](l)
  Multicospan(apx, legs; cat)
end 

""" Cast a cospan to a Multicospan """
Multicospan(s::Cospan{Ob,Hom}) where {Ob, Hom} = 
  Multicospan{Ob,Hom}(apex(s), legs(s))

""" Empty cospan """
Multicospan{Ob, Hom, Foot}(a::Ob) where {Ob, Hom, Foot}= 
  Multicospan{Ob, Hom}(a, Hom[], Foot[])

function Multicospan{Ob, Hom}(hs::AbstractVector{<:Hom}) where {Ob, Hom} 
  isempty(hs) && error("Multicospan needs an apex")   
  allequal(codom.(hs)) || error("Cospan codomains not equal")
  Multicospan{Ob, Hom}(codom(first(hs)), hs)
end

cone_objects(cospan::Multicospan) = feet(cospan)

@instance ThFreeDiagram{Int,Int,Union{Ob,Foot},Hom
                       } [model::Multicospan{Ob,Hom, Foot, V, W}
                         ] where {Ob,Hom,Foot,V,W} begin
  src(x::Int)::Int = x+1
  tgt(::Int)::Int = 1
  obmap(x::Int)::Union{Ob,Foot} = @match x begin 
    1 => apex(model)
    i => feet(model)[i-1]
  end
  hommap(i::Int)::Hom = model[i]
  obset()::FinSet = FinSet(length(model)+1)
  homset()::FinSet = FinSet(length(model))
end

""" Specialize a free diagram (can fail) """
function specialize(::Type{Multicospan}, d::FreeDiagram)
  es = homset(d)
  apex_v = only(unique(tgt.(Ref(d), es)))
  feet = obmap.(Ref(d), src.(Ref(d), es))
  Multicospan(obmap(d, apex_v), hommap.(Ref(d), es), feet)
end

""" Replace homs via a replacement function """
fmap(d::Multicospan, o, h, O::Type, H::Type) = 
  Multicospan{O,H,O}(o(apex(d))::O, Vector{H}(h.(legs(d))), Vector{O}(o.(feet(d))))

function untag(d::Multicospan{Ob,Hom}, i::Int, j::Int) where {Ob,Hom}
  O, H = untag(Ob, i), untag(Hom, j)
  Multicospan{O, H, O}(untag(d.apex, i), (x->untag(x, j)).(d.legs), (x->untag(x,i)).(d.feet))
end 
  
end # module
