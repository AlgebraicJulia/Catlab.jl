""" Arrow Category as a Double Category of Squares

In every category C, you can construct Sq(C) as a
[double category](https://ncatlab.org/nlab/show/double+category)
of commutative squares. This module uses SquareDiagrams to implement
this construction.
"""
module Squares

using AutoHashEquals

using ...GAT
using ...Theories: DoubleCategory
import ...Theories: ob, hom, dom, codom, compose, ⋅, ⋆, HomV, HomH,
                    composeH, composeV, id, idH, idV, id2, id2H, id2V
using ..FreeDiagrams, ..FinSets

@instance DoubleCategory{FinSet, FinFunction, FinFunction, SquareDiagram} begin
  @import dom, codom, top, bottom, left, right, ⋅
  idH(A::FinSet) = FinFunction(identity, A, A)
  idV(A::FinSet) = FinFunction(identity, A, A)

  composeH(f::FinFunction, g::FinFunction) = compose(f,g)
  composeV(f::FinFunction, g::FinFunction) = compose(f,g)

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
    f′= bottom(s₁)
    g = top(s₂)
    g′= bottom(s₂)
    return SquareDiagram(f⋅g, f′⋅g′, left(s₁), right(s₂))
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
    f′= right(s₁)
    g = left(s₂)
    g′= right(s₂)
    return SquareDiagram(top(s₁), bottom(s₂), f⋅g, f′⋅g′)
  end
end

end
