""" Commutative diagrams in a category.

**Note**: This module is at an early stage of construction. For now, only
commutative squares are implemented.
"""
module CommutativeDiagrams
export SquareDiagram, SquareOb, SquareHom, ob, hom, dom, codom, src, tgt,
  top, bottom, left, right

using StaticArrays: StaticVector, SVector
using StructEquality

using GATlab
using ...Theories: ThDoubleCategory
import ...Theories: ob, hom, dom, codom, src, tgt, top, bottom,
  compose, id, pcompose, pid, ⋅, *
import ..FreeDiagrams: left, right

# Commutative squares
#####################

""" Commutative square in a category.

Commutative squares in a category ``C`` form the cells of a strict double
category, the *arrow double category* or *double category of squares* in ``C``,
with composition in both directions given by pasting of commutative squares.

In this data structure, the four morphisms comprising the square are stored as a
static vector of length 4, ordered as domain (top), codomain (bottom), source
(left), and target (right). This convention agrees with the GAT for double
categories (`ThDoubleCategory`).
"""
@struct_hash_equal struct SquareDiagram{Hom,Homs<:StaticVector{4,Hom}}
  homs::Homs
end

function SquareDiagram(top, bottom, left, right)
  dom(top) == dom(left) ||
    error("Domain mismatch in top-left corner: $top vs $left")
  codom(top) == dom(right) ||
    error("Domain mismatch top-right corner: $top vs $right")
  dom(bottom) == codom(left) ||
    error("Domain mismatch in bottom-left corner: $bottom vs $left")
  codom(bottom) == codom(right) ||
    error("Domain mismatch in bottom-right corner: $bottom vs $right")
  SquareDiagram(SVector(top, bottom, left, right))
end

ob(sq::SquareDiagram) =
  SVector(dom(top(sq)), codom(top(sq)), dom(bottom(sq)), codom(bottom(sq)))
hom(sq::SquareDiagram) = sq.homs

top(sq::SquareDiagram) = sq.homs[1]
bottom(sq::SquareDiagram) = sq.homs[2]
left(sq::SquareDiagram) = sq.homs[3]
right(sq::SquareDiagram) = sq.homs[4]

""" Object in the double category of squares.

See also: [`SquareDiagram`](@ref).
"""
@struct_hash_equal struct SquareOb{Ob}
  ob::Ob
end

ob(x::SquareOb) = x.ob

""" Arrow or proarrow in the double category of squares.

See also: [`SquareDiagram`](@ref).
"""
@struct_hash_equal struct SquareHom{Hom}
  hom::Hom
end

hom(f::SquareHom) = f.hom

@instance ThDoubleCategory{SquareOb,SquareHom,SquareHom,SquareDiagram} begin
  dom(f::SquareHom) = SquareOb(dom(hom(f)))
  codom(f::SquareHom) = SquareOb(codom(hom(f)))
  src(m::SquareHom) = SquareOb(dom(hom(m)))
  tgt(m::SquareHom) = SquareOb(codom(hom(m)))

  dom(α::SquareDiagram) = SquareHom(top(α))
  codom(α::SquareDiagram) = SquareHom(bottom(α))
  src(α::SquareDiagram) = SquareHom(left(α))
  tgt(α::SquareDiagram) = SquareHom(right(α))

  compose(f::SquareHom, g::SquareHom) = SquareHom(compose(hom(f), hom(g)))
  id(x::SquareOb) = SquareHom(id(ob(x)))

  pcompose(m::SquareHom, n::SquareHom) = SquareHom(compose(hom(m), hom(n)))
  pid(x::SquareOb) = SquareHom(id(ob(x)))

  function compose(α::SquareDiagram, β::SquareDiagram)
    bottom(α) == top(β) || error("Domain mismatch: $(bottom(α)) != $(top(β))")
    SquareDiagram(SVector(
      top(α), bottom(β), left(α)⋅left(β), right(α)⋅right(β)))
  end
  function id(m::SquareHom)
    f = hom(m)
    SquareDiagram(f, f, id(dom(f)), id(codom(f)))
  end

  function pcompose(α::SquareDiagram, β::SquareDiagram)
    right(α) == left(β) || error("Domain mismatch: $(right(α)) != $(left(β))")
    SquareDiagram(SVector(
      top(α)⋅top(β), bottom(α)⋅bottom(β), left(α), right(β)))
  end
  function pid(f::SquareHom)
    f = hom(f)
    SquareDiagram(id(dom(f)), id(codom(f)), f, f)
  end
end

end
