module ConstEitherFn 

export ConstEither

using StructEquality

using GATlab

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction

"""
A map out A + C -> B + C, where we interpret C as constant. Because these use 
UnionSets rather than disjoint sets, any overlap between A and C gets treated 
as constant.
"""
@struct_hash_equal struct ConstEither
  fun::SetFunction
  dom::AbsSet
  codom::AbsSet
  function ConstEither(f, d, c)
    ed, ec = getvalue(d), getvalue(c)
    ed isa UnionSet && left(ed) == dom(f) || error("f domain mismatch")
    ec isa UnionSet && left(ec) == codom(f) || error("f codomain mismatch")
    right(ec) == right(ed) || error("UnionSet right sets don't match")
    new(f, d, c)
  end
end

# Accessor
##########
GATlab.getvalue(c::ConstEither) = c.fun

# SetFunction implementation
############################

@instance ThSetFunction [model::ConstEither] begin

  dom()::AbsSet = model.dom

  codom()::AbsSet = model.codom

  app(i::Any)::Any = 
    i ∈ right(getvalue(model.codom)) ? i : getvalue(model)(i)

  postcompose(f::AbsFunction)::AbsFunction = 
    SetFunction(ConstEither(f(getvalue(model)), model.dom, codom[model](f)))

end

end # module
