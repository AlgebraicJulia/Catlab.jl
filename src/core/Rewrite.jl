""" Rewriting for GAT expressions.

The current content of this module is just a stopgap until I can implement
a generic term rewriting system.
"""
module Rewrite
export associate, associate_unit, distribute_unary, involute

using Compat
using ..Syntax

""" Simplify associative binary operation.

Maintains the normal form `op(e1,e2,...)` where `e1`,`e2`,... are expressions
that are *not* applications of `op()`
"""
function associate(expr::E)::E where E <: GATExpr
  op, e1, e2 = head(expr), first(expr), last(expr)
  args1 = head(e1) == op ? args(e1) : [e1]
  args2 = head(e2) == op ? args(e2) : [e2]
  E([args1; args2], type_args(expr))
end

""" Simplify associative binary operation with unit.

Reduces a freely generated (typed) monoid to normal form.
"""
function associate_unit(expr::GATExpr, unit::Function)::GATExpr
  e1, e2 = first(expr), last(expr)
  if (head(e1) == nameof(unit)) e2
  elseif (head(e2) == nameof(unit)) e1
  else associate(expr) end
end

""" Distribute unary operation over binary operation.
"""
function distribute_unary(expr::GATExpr, unary::Function, binary::Function;
                          unit::Union{Function,Nothing}=nothing,
                          contravariant::Bool=false)::GATExpr
  if (head(expr) != nameof(unary)) return expr end
  @assert length(args(expr)) == 1
  arg = first(expr)
  if head(arg) == nameof(binary)
    binary(map(unary, (contravariant ? reverse : identity)(args(arg))))
  elseif !isnothing(unit) && head(arg) == nameof(unit)
    arg
  else
    expr
  end
end

""" Simplify involutive unary operation.
"""
function involute(expr::GATExpr)
  @assert length(args(expr)) == 1
  arg = first(expr)
  head(expr) == head(arg) ? first(arg) : expr
end

end
