export Slice, SliceHom

using StructEquality

using GATlab
using ....Theories: ThCategory
import ....Theories: dom, codom, compose, id
import ....BasicSets: force

"""
The data of the object of a slice category (say, some category C sliced over an
object X in Ob(C)) is the data of a homomorphism in Hom(A,X) for some ob A.
"""
@struct_hash_equal struct Slice{Hom}
  slice::Hom
end

"""
The data of the morphism of a slice category (call it h, and suppose a category
C is sliced over an object X in Ob(C)) between objects f and g is a homomorphism
in the underlying category that makes the following triangle commute.

   h
A --> B
f ↘ ↙ g
   X
"""
@struct_hash_equal struct SliceHom{Hom, Dom<:Slice, Codom<:Slice}
  dom::Dom
  codom::Codom
  f::Hom
end

function SliceHom(d::Dom, cd::Codom, f::Hom; strict::Bool=true) where {Dom,Codom,Hom}
  !strict || codom(d) == codom(cd) || error("$d and $cd not in same category")
  !strict || dom(d) == dom(f) || error("dom $d does not match $f")
  !strict || dom(cd) == codom(f) || error("codom $cd does not match $f")
  return SliceHom{Hom,Dom,Codom}(d, cd, f)
end

dom(s::Slice) = dom(s.slice)
codom(s::Slice) = codom(s.slice)
force(s::Slice)  = Slice(force(s.slice))
force(s::SliceHom) = SliceHom(
  force(dom(s)), force(codom(s)), force(s.f))


@instance ThCategory{Slice, SliceHom} begin
  dom(f::SliceHom) = f.dom
  codom(f::SliceHom) = f.codom
  id(A::Slice) = SliceHom(A, A, id(dom(A.slice)))
  function compose(f::SliceHom, g::SliceHom)
    SliceHom(dom(f), codom(g), compose(f.f, g.f))
  end
end

