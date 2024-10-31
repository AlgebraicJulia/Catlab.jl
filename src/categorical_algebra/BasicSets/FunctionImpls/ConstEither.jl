
# ConstEither 
#------------
"""
A map out A + C -> B + C, where we interpret C as constant. Because these use 
EitherSets rather than disjoint sets, any overlap between A and C gets treated 
as constant.
"""
@struct_hash_equal struct ConstEither <: SetFunctionImpl
  fun::SetFunction
  dom::AbsSet
  codom::AbsSet
  function ConstEither(f, d, c)
    ed, ec = getvalue(d), getvalue(c)
    ed isa EitherSet && left(ed) == dom(f) || error("f domain mismatch")
    ec isa EitherSet && left(ec) == codom(f) || error("f codomain mismatch")
    right(ec) == right(ed) || error("EitherSet right sets don't match")
    new(f, d, c)
  end
end

getvalue(c::ConstEither) = c.fun

# SetFunction implementation

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::ConstEither] begin
  dom()::AbsSet = model.dom

  codom()::AbsSet = model.codom

  app(i::Any)::Any = 
    i ∈ right(getvalue(model.codom)) ? i : getvalue(model)(i)

  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(ConstEither(f(getvalue(model)), model.dom, codom[model](f)))
end
