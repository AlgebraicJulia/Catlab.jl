module Multispans 

export Multispan, Multicospan

using StructEquality, MLStyle
using GATlab 

using .....BasicSets: FinSet
using ...FreeDiagrams: ThFreeDiagram, FreeDiagram
import ...FreeDiagrams: fmap, cone_objects, cocone_objects

using ..Spans: Multi_Co_Span, Span, Cospan, apex
import ..Spans: feet, legs

using .ThCategory: dom, codom

# Common to spans and cospans
#############################

abstract type MultiSpanCospan{Ob,Hom} <: Multi_Co_Span{Ob,Hom} end

Base.getindex(m::MultiSpanCospan, i) = legs(m)[i]

legs(m::MultiSpanCospan) = m.legs

function left(s::MultiSpanCospan) 
  length(s) == 2 || error("Span/Cospan does has $(length(s)) legs")
  first(legs(s))
end

function right(s::MultiSpanCospan) 
  length(s) == 2 || error("Span/Cospan does has $(length(s)) legs")
  last(legs(s))
end


# Multispans 
#-----------

@struct_hash_equal struct Multispan{Ob, Hom} <: MultiSpanCospan{Ob,Hom}
  apex::Ob
  legs::AbstractVector{Hom}
  function Multispan{Ob, Hom}(apex,legs) where {Ob,Hom}
    baddoms = [dom(l) for l in legs if dom(l)!=apex]
    isempty(baddoms) || error("Bad span $baddoms != $apex")
    new{Ob,Hom}(apex, legs)
  end
end


""" infer types """
Multispan(apex::Ob,legs::AbstractVector{Hom}) where {Ob,Hom} = 
  Multispan{Ob,Hom}(apex, legs)

""" Construct from just a list, assuming it's nonempty """
Multispan(legs::AbstractVector) = Multispan(dom(first(legs)), legs)

""" Cast a span to a Multispan """
Multispan(s::Span{Ob,Hom}) where {Ob, Hom} = Multispan{Ob,Hom}(apex(s), legs(s))

""" Empty span """
Multispan{Ob, Hom}(a::Ob) where {Ob, Hom} = Multispan{Ob, Hom}(a, Hom[])


function Multispan{Ob, Hom}(hs::AbstractVector{<:Hom}) where {Ob, Hom} 
  isempty(hs) && error("Multispan needs an apex")   
  allequal(dom.(hs)) || error("Span domains not equal")
  Multispan{Ob, Hom}(dom(first(hs)), hs)
end

feet(m::Multispan) = codom.(legs(m))

cocone_objects(span::Multispan) = feet(span)

""" Replace homs via a replacement function """
fmap(d::T, o, h) where T<:Multi_Co_Span  = T(o(apex(d)), h.(legs(d)))


@instance ThFreeDiagram{Int,Int,Ob,Hom,FinSet
                       } [model::Multispan{Ob,Hom}] where {Ob, Hom} begin
  src(::Int)::Int = 1
  tgt(x::Int)::Int = x+1
  obmap(x::Int)::Ob = @match x begin 
    1 => apex(model)
    i => codom(model[i-1])
  end
  hommap(i::Int)::Hom = model[i]
  obset()::FinSet = FinSet(length(model)+1)
  homset()::FinSet = FinSet(length(model))
end


""" Specialize a free diagram (can fail) """
function Multispan(d::FreeDiagram)
  hs = hom_map.(Ref(d), homset(d))
  Multispan(ob_map(d, first(homset(d))), hs)
end

# Multicospans 
#-------------

@struct_hash_equal struct Multicospan{Ob, Hom} <: MultiSpanCospan{Ob, Hom}
  apex::Ob
  legs::AbstractVector{Hom}
  function Multicospan{Ob, Hom}(apex,legs) where {Ob,Hom}
    all([codom(l)==apex for l in legs]) || error("Bad cospan")
    new{Ob,Hom}(apex, legs)
  end
end

""" infer types """
Multicospan(apex::Ob,legs::AbstractVector{Hom}) where {Ob,Hom} = 
  Multicospan{Ob,Hom}(apex, legs)

""" Construct from just a list, assuming it's nonempty """
Multicospan(legs::AbstractVector) = Multicospan(codom(first(legs)), legs)


""" Cast a cospan to a Multicospan """
Multicospan(s::Cospan{Ob,Hom}) where {Ob, Hom} = 
  Multicospan{Ob,Hom}(apex(s), legs(s))

""" Empty cospan """
Multicospan{Ob, Hom}(a::Ob) where {Ob, Hom}= Multicospan{Ob, Hom}(a, Hom[])

function Multicospan{Ob, Hom}(hs::AbstractVector{<:Hom}) where {Ob, Hom} 
  isempty(hs) && error("Multicospan needs an apex")   
  allequal(codom.(hs)) || error("Cospan codomains not equal")
  Multicospan{Ob, Hom}(codom(first(hs)), hs)
end

feet(m::Multicospan) = dom.(legs(m))

cone_objects(cospan::Multicospan) = feet(cospan)

@instance ThFreeDiagram{Int,Int,Ob,Hom,FinSet
                       } [model::Multicospan{Ob,Hom}] where {Ob, Hom} begin
  src(x::Int)::Int = x+1
  tgt(::Int)::Int = 1
  obmap(x::Int)::Ob = @match x begin 
    1 => apex(model)
    i => dom(model[i-1])
  end
  hommap(i::Int)::Hom = model[i]
  obset()::FinSet = FinSet(length(model)+1)
  homset()::FinSet = FinSet(length(model))
end

""" Specialize a free diagram (can fail) """
function Multicospan(d::FreeDiagram)
  hs = hom_map.(Ref(d), homset(d))
  Multiscopan(ob_map(d, first(homset(d))), hs)
end

end # module
