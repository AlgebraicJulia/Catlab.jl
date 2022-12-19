module TypeUtils
export pi_type, pi_type_elt, genericize

""" Creates a named tuple type
"""
function pi_type(types::Vector{Tuple{Symbol, Type}})
  NamedTuple{Tuple(map(t -> t[1], types)), Tuple{map(t -> t[2], types)...}}
end

""" Creates a quoted element of a named tuple
"""
function pi_type_elt(exprs::Vector{Tuple{Symbol, Expr}})
  Expr(:tuple, Expr(:parameters, [Expr(:kw, f, e) for (f,e) in exprs]...))
end

"""
The type variables that we have generated might not match up with the type
variables that are created as generic parameters to the struct acset, this is a
way of making the two line up
"""
function genericize(T::Type, tvars::Vector{TypeVar})
  occuring_variables = []
  cur = T
  for tvar in reverse(tvars)
    next = UnionAll(tvar, cur)
    if typeof(next) == UnionAll && next.var == tvar
      push!(occuring_variables, tvar)
      cur = next
    end
  end
  if length(occuring_variables) > 0
    :($cur{$([tvar.name for tvar in reverse(occuring_variables)]...)})
  else
    cur
  end
end

end
