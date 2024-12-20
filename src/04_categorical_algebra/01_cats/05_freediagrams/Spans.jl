module Spans
export apex, legs, feet, Span, Cospan

using StructEquality, MLStyle
using GATlab 

using .....BasicSets: FinSet
import .....BasicSets: left, right
using ...FreeDiagrams: ThFreeDiagram, FreeDiagram
import ...FreeDiagrams: fmap, cone_objects, cocone_objects

using .ThCategory: dom, codom

# Generic code to both (multi)(co)spans 
#--------------------------------------
abstract type Multi_Co_Span{Ob,Hom} end

apex(m::Multi_Co_Span) = m.apex

Base.length(m::Multi_Co_Span) = length(legs(m)) 

Base.iterate(m::Multi_Co_Span, x...) = iterate(legs(m), x...)

# Generic code to both spans and cospans 
#---------------------------------------

abstract type SpanCospan{Ob,Hom} <: Multi_Co_Span{Ob,Hom} end

legs(m::SpanCospan) = [left(m), right(m)]

left(s::SpanCospan) = s.left 

right(s::SpanCospan) = s.right 

objects(s::Multi_Co_Span) = [apex(s), feet(s)...]


# Spans 
#-----------

@struct_hash_equal struct Span{Ob, Hom} <: SpanCospan{Ob,Hom}
  apex::Ob
  left::Hom
  right::Hom
  function Span{Ob, Hom}(f, g) where {Ob, Hom}
    dom(f) == dom(g) || error("Cannot make span from $f and $g") 
    new{Ob,Hom}(dom(f), f, g)
  end
end

Span(f::Hom, g::Hom) where Hom = Span{typeof(dom(f)),Hom}(f, g)

feet(m::Span) = codom.(legs(m))

""" We naturally take colimits of spans, but not limits """
cocone_objects(span::Span) = feet(span)

""" Replace homs via a replacement function """
fmap(d::Span, _, h) = Span(h(left(d)), h(right(d)))

@instance ThFreeDiagram{Int,Int,Ob,Hom,FinSet} [model::Span{Ob,Hom}] where {Ob, Hom} begin
  src(::Int)::Int = 1
  tgt(x::Int)::Int = x+1
  obmap(x::Int)::Ob = @match x begin 
    1 => apex(model)
    2 => codom(left(model))
    3 => codom(right(model))
  end
  hommap(x::Int)::Hom = (x === 1 ? left : right)(model)
  obset()::FinSet = FinSet(3)
  homset()::FinSet = FinSet(2)
end

# Cospans
#--------
#TODO add domfun and codfun which default to ThCategory.dom/.codom
@struct_hash_equal struct Cospan{Ob, Hom} <: SpanCospan{Ob,Hom}
  apex::Ob
  left::Hom
  right::Hom
  function Cospan{Ob, Hom}(f, g) where {Ob, Hom}
    codom(f) == codom(g) || error("Cannot make cospan from $f and $g") 
    new{Ob,Hom}(codom(f), f, g)
  end
end

Cospan(f::Hom, g::Hom) where Hom = Cospan{typeof(dom(f)),Hom}(f, g)

feet(m::Cospan) = dom.(legs(m))

fmap(d::Cospan, _, h) = Cospan(h(left(d)), h(right(d)))

@instance ThFreeDiagram{Int,Int,Ob,Hom,FinSet} [model::Cospan{Ob,Hom}] where {Ob, Hom} begin
  src(x::Int)::Int = x+1
  tgt(::Int)::Int = 1
  obmap(x::Int)::Ob = @match x begin 
    1 => apex(model)
    2 => dom(left(model))
    3 => dom(right(model))
  end
  hommap(x::Int)::Hom = (x === 1 ? left : right)(model)
  obset()::FinSet = FinSet(3)
  homset()::FinSet = FinSet(2)
end


""" We naturally take limits of cospans, but not colimits """
cone_objects(cospan::Cospan) = feet(cospan)

end # module
