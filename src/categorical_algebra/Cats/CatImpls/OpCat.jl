
""" Opposite category, where morphism are reversed.

Call `op(::Cat)` instead of directly instantiating this type.
"""
@struct_hash_equal struct OppositeCat{Ob,Hom} <: CatImpl{Ob,Hom}
  cat::Category{Ob,Hom}
end

getvalue(c::OppositeCat) = c.cat

op(c::Cat) = Category(OppositeCat(c))

@instance ThCategory{Ob,Hom} [model::OppositeCat{Ob,Hom}] where {Ob,Hom} begin
  dom(f::Hom) = codom(getvalue(model), f)

  codom(f::Hom) = dom(getvalue(model), f)

  id(x::Ob) = id(getvalue(model), x)

  compose(f::Hom,g::Hom) = compose(getvalue(model), g, f)
end