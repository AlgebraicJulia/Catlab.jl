module CopairedFinDomFunctions 

export CopairedFinDomFunction

using StructEquality

using GATlab
import ACSets.Columns: preimage 

using ..BasicSets
using .ThFinDomFunction

"""
Interpret a FinDomFunction f: D → L + R as a function D + R → L + R 
"""
@struct_hash_equal struct CopairedFinDomFunction{R′,D′,L′}
  val::FinDomFunction
  R::SetOb
  D::FinSet
  L::AbsSet
  function CopairedFinDomFunction(fdf::FinDomFunction)
    c = getvalue(codom(fdf))
    c isa EitherSet || error("Can only create CopairedFinDomFunction when codomain is of the form A+B, not $c")
    new{eltype(right(c)), eltype(dom(fdf)), eltype(left(c))}(fdf, right(c), dom(fdf), left(c))
  end
end


Base.get(f::CopairedFinDomFunction) = f.val

@instance ThSetFunction{Union{Left{D},Right{R}},Union{Left{L}, Right{R}}
                       } [model::CopairedFinDomFunction{R,D,L}] where {R,D,L} begin

  dom()::SetOb = either(model.D, model.R)

  codom()::SetOb = either(model.L, model.R) # == codom(model.val)

  app(x::Union{Left{D},Right{R}}) = if x isa Left
    app(model.val, getvalue(x))
  else
    x
  end

  # generically compose the two functions, nothing special we can say
  function postcompose(f::SetFunction′)::SetFunction′ 
    if getvalue(f) isa CopairedFinDomFunction
      SetFunction(CopairedFinDomFunction(postcompose(get(model), f)))
    else 
      SetFunction(SetFunction(model), f) # generically compose
    end
  end

end


""" We can also construct this given just f′: D → L  by letting f = f′⋅ι """
function CopairedFinDomFunction(f′::Union{FinFunction, FinDomFunction}, R::SetOb)
  ι = FinDomFunction(x->Left(x), codom(f′), either(codom(f′), R))
  f = postcompose(f, ι)
  CopairedFinDomFunction(f)
end


""" The preimage of a Left can only come from the FinDomFunction part """
preimage(f::CopairedFinDomFunction, l::Left) = preimage(get(f), l)

end # module
