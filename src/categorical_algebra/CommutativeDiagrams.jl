""" Commutative diagrams in a category.

**NOTE**: This module is at an early stage of construction. At this time, only
commutative squares are implemented.
"""
module CommutativeDiagrams
export SquareDiagram, ob, hom, left, right, top, bottom

using AutoHashEquals

using ...GAT
using ...Theories: DoubleCategory
import ...Theories:
  ob,
  hom,
  dom,
  codom,
  compose,
  ⋅,
  ⋆,
  HomV,
  HomH,
  composeH,
  composeV,
  id,
  idH,
  idV,
  id2,
  id2H,
  id2V,
  left,
  right,
  top,
  bottom
using ..FinSets

# Commutative squares
#####################

"""    SquareDiagram(top, bottom, left, right)

Creates a square diagram in a category, which forms the 2-cells of the double
category Sq(C). The four 1-cells are given in top, bottom, left, right order, to
match the GAT of a double category.
"""
@auto_hash_equals struct SquareDiagram{Ob,Hom,Homs<:AbstractVector{Hom}}
  corners::Vector{Ob}
  sides::Homs
end

function SquareDiagram(homs::AbstractVector)
  length(homs) == 4 || error(
    "Square diagrams accept exactly 4 homs, in order top, bottom, left, right",
  )
  obs = [dom(homs[1]), dom(homs[2]), dom(homs[4]), codom(homs[4])]

  # checking well-formedness
  # top-left share domains
  @assert dom(homs[1]) == dom(homs[3])
  # bottom-right share codomains
  @assert codom(homs[2]) == codom(homs[4])
  # left-bottom intersection
  @assert codom(homs[3]) == dom(homs[2])
  # top-right intersection
  @assert codom(homs[1]) == dom(homs[4])

  SquareDiagram(obs, homs)
end

SquareDiagram(top, bottom, left, right) =
  SquareDiagram([top, bottom, left, right])

ob(sq::SquareDiagram) = sq.corners
hom(sq::SquareDiagram) = sq.sides

top(sq::SquareDiagram) = sq.sides[1]
bottom(sq::SquareDiagram) = sq.sides[2]
left(sq::SquareDiagram) = sq.sides[3]
right(sq::SquareDiagram) = sq.sides[4]

""" Arrow category of FinSet as a double category of commutative squares.

For any category C, you can construct Sq(C) as a
[double category](https://ncatlab.org/nlab/show/double+category)
of commutative squares.

TODO: This construction has nothing specifically to do with finite sets and
functions and should be generalized to any category C.
"""
@instance DoubleCategory{FinSet,FinFunction,FinFunction,SquareDiagram} begin
  @import dom, codom, top, bottom, left, right, ⋅
  idH(A::FinSet) = FinFunction(identity, A, A)
  idV(A::FinSet) = FinFunction(identity, A, A)

  composeH(f::FinFunction, g::FinFunction) = compose(f, g)
  composeV(f::FinFunction, g::FinFunction) = compose(f, g)

  id2(A::FinSet) = SquareDiagram(idH(A), idH(A), idV(A), idV(A))
  # FIXME: how do you distinguish between vertical and horizontal if they are the same type?
  id2V(f::FinFunction) = SquareDiagram(f, f, idV(A), idV(A))
  id2H(f::FinFunction) = SquareDiagram(idH(A), idH(A), f, f)

  """    composeH(s₁, s₂)

  compose two squares horizontally as shown below:
      1   -f->   3  -g->   5
      |          |         |
      |          |         |
      v          v         v
      2  -f'->   4  -g'->  6
   """
  function composeH(s₁::SquareDiagram, s₂::SquareDiagram)
    @assert ob(s₁)[3] == ob(s₂)[1]
    @assert ob(s₁)[4] == ob(s₂)[2]
    @assert right(s₁) == left(s₂)

    f = top(s₁)
    f′ = bottom(s₁)
    g = top(s₂)
    g′ = bottom(s₂)
    return SquareDiagram(f ⋅ g, f′ ⋅ g′, left(s₁), right(s₂))
  end

  """    composeV(s₁, s₂)

  compose two squares vertically as shown below:
      1   -->  3
      |        |
      |        |
      v        v
      2  -->   4
      |        |
      |        |
      v        v
      5  -->   6
  """
  function composeV(s₁::SquareDiagram, s₂::SquareDiagram)
    @assert ob(s₁)[2] == ob(s₂)[1]
    @assert ob(s₁)[4] == ob(s₂)[3]
    @assert bottom(s₁) == top(s₂)

    f = left(s₁)
    f′ = right(s₁)
    g = left(s₂)
    g′ = right(s₂)
    return SquareDiagram(top(s₁), bottom(s₂), f ⋅ g, f′ ⋅ g′)
  end
end

end
