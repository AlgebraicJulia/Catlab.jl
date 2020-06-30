""" Diagrams of a given shape.
"""
module ShapeDiagrams
export Span, Cospan, left, right, apex, base

using ...Theories: dom, codom

""" Span of morphisms in a category.
"""
struct Span{Left,Right}
  left::Left
  right::Right
  
  function Span(left::Left, right::Right; strict::Bool=true) where {Left,Right}
    if strict && dom(left) != dom(right)
      error("Domains of legs in span do not match: $left vs $right")
    end
    new{Left,Right}(left, right)
  end
end

apex(span::Span) = dom(span.left) # == dom(span.right)
left(span::Span) = span.left
right(span::Span) = span.right

""" Cospan of morphisms in a category.
"""
struct Cospan{Left,Right}
  left::Left
  right::Right
  
  function Cospan(left::Left, right::Right; strict::Bool=true) where {Left,Right}
    if strict && codom(left) != codom(right)
      error("Codomains of legs in cospan do not match: $left vs $right")
    end
    new{Left,Right}(left, right)
  end
end

base(cospan::Cospan) = codom(cospan.left) # == codom(cospan.right)
left(cospan::Cospan) = cospan.left
right(cospan::Cospan) = cospan.right

""" Decorate Cospan of morphisms for representing open networks.
"""
struct DecoratedCospan{Left,Right,Decoration}
  cospan::Cospan{Left,Right}
  decoration::Decoration
end

decoration(m::DecoratedCospan) = m.decoration
undecorate(m::DecoratedCospan) = m.cospan
dom(m::DecoratedCospan) = dom(m.cospan)
codom(m::DecoratedCospan) = codom(m.cospan)
base(m::DecoratedCospan) = base(m.cospan)
left(m::DecoratedCospan) = left(m.cospan)
right(m::DecoratedCospan) = right(m.cospan)

end
