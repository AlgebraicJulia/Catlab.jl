""" General-purpose tools for metaprogramming in Julia.
"""
module Meta
export Expr0, JuliaFunction, JuliaFunctionSig, parse_function,
  parse_function_sig, generate_function, append_expr!, concat_expr,
  replace_symbols, strip_lines

using AutoHashEquals
using Match

# Data types
############

const Expr0 = Union{Symbol,Expr}

@auto_hash_equals immutable JuliaFunction
  call_expr::Expr
  return_type::Nullable{Expr0}
  impl::Nullable{Expr}
  
  function JuliaFunction(call_expr, return_type=Nullable(), impl=Nullable()) 
    new(call_expr, return_type, impl)
  end
end

@auto_hash_equals immutable JuliaFunctionSig
  name::Symbol
  types::Vector{Expr0}
end

# Parsing Julia functions
#########################

""" Parse Julia function definition into standardized form.
"""
function parse_function(expr::Expr)::JuliaFunction
  fun_expr, impl = @match expr begin
    Expr(:(=), args, _) => args
    Expr(:function, args, _) => args
    _ => throw(ParseError("Ill-formed function definition $expr"))
  end
  @match fun_expr begin
    (Expr(:(::), [Expr(:call, args, _), return_type], _) => 
      JuliaFunction(Expr(:call, args...), return_type, impl))
    (Expr(:call, args, _) =>
      JuliaFunction(Expr(:call, args...), Nullable(), impl))
    _ => throw(ParseError("Ill-formed function header $fun_expr"))
  end
end

""" Parse signature of Julia function.
"""
function parse_function_sig(call_expr::Expr)::JuliaFunctionSig
  name, args = @match call_expr begin
    Expr(:call, [name::Symbol, args...], _) => (name, args)
    _ => throw(ParseError("Ill-formed function signature $call_expr"))
  end
  types = [ @match expr begin
      Expr(:(::), [_, typ], _) => typ
      Expr(:(::), [typ], _) => typ
      _ => :Any
    end for expr in args ]
  JuliaFunctionSig(name, types)
end
parse_function_sig(fun::JuliaFunction) = parse_function_sig(fun.call_expr)

""" Generate Julia expression for function definition.
"""
function generate_function(fun::JuliaFunction)::Expr
  if isnull(fun.return_type)
    head = fun.call_expr
  else 
    head = Expr(:(::), fun.call_expr, get(fun.return_type))
  end
  if isnull(fun.impl)
    body = Expr(:block)
  else
    # Wrap implementation inside block if not already.
    impl = get(fun.impl)
    body = impl.head == :block ? impl : Expr(:block, impl)
  end
  Expr(:function, head, body)
end

# Operations on Julia expressions
#################################

""" Append a Julia expression to a block expression.
"""
function append_expr!(block::Expr, expr)::Expr
  @assert block.head == :block
  @match expr begin
    Expr(:block, args, _) => append!(block.args, args)
    _ => push!(block.args, expr)
  end
  block
end

""" Concatenate two Julia expressions into a block expression.
"""
function concat_expr(expr1::Expr, expr2::Expr)::Expr
  @match (expr1, expr2) begin
    (Expr(:block, a1, _), Expr(:block, a2, _)) => Expr(:block, [a1; a2]...)
    (Expr(:block, a1, _), _) => Expr(:block, [a1; expr2]...)
    (_, Expr(:block, a2, _)) => Expr(:block, [expr1; a2]...)
    _ => Expr(:block, expr1, expr2)
  end
end

""" Replace symbols occurring anywhere in a Julia function.
"""
function replace_symbols(bindings::Dict, f::JuliaFunction)::JuliaFunction
  JuliaFunction(
    replace_symbols(bindings, f.call_expr),
    isnull(f.return_type) ? Nullable() :
      replace_symbols(bindings, get(f.return_type)),
    isnull(f.impl) ? Nullable() :
      replace_symbols(bindings, get(f.impl)),
  )
end

""" Replace symbols occuring anywhere in a Julia expression.
"""
function replace_symbols(bindings::Dict, expr)
  recurse(expr) = replace_symbols(bindings, expr)
  @match expr begin
    Expr(head, args, _) => Expr(head, map(recurse,args)...)
    sym::Symbol => get(bindings, sym, sym)
    _ => expr
  end
end

""" Remove all :line annotations from a Julia expression.
"""
function strip_lines(expr::Expr; recurse::Bool=false)::Expr
  args = filter(x -> !(isa(x, Expr) && x.head == :line), expr.args)
  if recurse
    args = [ isa(x, Expr) ? strip_lines(x; recurse=true) : x for x in args ]
  end
  Expr(expr.head, args...)
end

end
