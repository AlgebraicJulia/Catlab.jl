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

  composeH(α::SquareDiagram, β::SquareDiagram) = hcompose(α, β)
  composeV(α::SquareDiagram, β::SquareDiagram) = vcompose(α, β)

end

end
