module CoprodFunctions 

export CoprodFunction

using StructEquality

using GATlab
import ACSets.Columns: preimage 

using ..BasicSets

using .ThSetFunction

"""
Interpret a pair of functions f: A -> B and g: C -> D as a function A+C -> B+D
"""
@struct_hash_equal struct CoprodFunction{L, R, LDom<:AbsSet, LCod<:AbsSet, RDom<:AbsSet, RCod<:AbsSet, LD, LC, RD, RC}
  lft::WithModel{L}
  rght::WithModel{R}
  ldom::LDom
  lcod::LCod
  rdom::RDom
  rcod::RCod

  function CoprodFunction(lft::AbstractFunction, rght::AbstractFunction)
    sets = dom(lft), codom(lft), dom(rght), codom(rght)
    LR = WithModel.(getvalue([lft, rght]))
    params = [typeof.(LR); typeof.(sets); eltype.(sets)]
    new{params...}(LR..., sets...)
  end
end

@instance ThSetFunction{Union{Left{LD}, Right{RD}}, Union{Left{LC}, Right{RC}}
    } [model::CoprodFunction{L,R,SetOb,SetOb,SetOb,SetOb,LD, LC, RD, RC}
      ] where {L, R, LD, LC, RD, RC} begin

  dom()::SetOb = either(model.ldom, model.rdom)

  codom()::SetOb = either(model.rcod, model.rcod)

  app(x::Union{Left{LD}, Right{RD}})::Union{Left{LC}, Right{RC}} = if x isa Left
    app(model.lft, getvalue(x))
  else
    app(model.rght, getvalue(x))
  end

  function postcompose(f::SetFunction′)::SetFunction′ 
    error("TODO $model postcompose with $f")
  end

end


preimage(f::CoprodFunction, l::Left) = Left.(preimage(f.lft, getvalue(l)))
preimage(f::CoprodFunction, r::Right) = Right.(preimage(f.rght, getvalue(r)))

end # module
