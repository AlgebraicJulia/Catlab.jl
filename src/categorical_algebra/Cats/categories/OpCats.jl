module OpCats
export OppositeCat, op

using StructEquality

import GATlab: op

using ..Categories
import ..Categories: ob, hom, dom, codom, id, compose

""" Opposite category, where morphism are reversed.

Call `op(::Cat)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeCat{Ob,Hom,Size<:CatSize,C<:Cat{Ob,Hom,Size}} <:
    Cat{Ob,Hom,Size}
  cat::C
end

ob(C::OppositeCat, x) = ob(C.cat, x)
hom(C::OppositeCat, f) = hom(C.cat, f)

dom(C::OppositeCat, f) = codom(C.cat, f)
codom(C::OppositeCat, f) = dom(C.cat, f)
id(C::OppositeCat, x) = id(C.cat, x)
compose(C::OppositeCat, f, g) = compose(C.cat, g, f)

""" Oppositization 2-functor.

The oppositization endo-2-functor on Cat, sending a category to its opposite, is
covariant on objects and morphisms and contravariant on 2-morphisms, i.e., is a
2-functor ``op: Catᶜᵒ → Cat``. For more explanation, see the
[nLab](https://ncatlab.org/nlab/show/opposite+category).
"""
op(C::Cat) = OppositeCat(C)
op(C::OppositeCat) = C.cat

end # module
