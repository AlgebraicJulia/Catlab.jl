""" General-purpose tools for metaprogramming in Julia.
"""
module Meta
export Expr0, JuliaFunction, JuliaFunctionSig, parse_docstring, parse_function,
  parse_function_sig, generate_docstring, generate_function,
  append_expr!, concat_expr, replace_symbols, strip_lines

using Base.Meta: ParseError
using Compat
using AutoHashEquals
using Match

# Data types
############

const Expr0 = Union{Symbol,Expr}

@auto_hash_equals struct JuliaFunction
  call_expr::Expr
  return_type::Union{Expr0,Nothing}
  impl::Union{Expr,Nothing}
  doc::Union{String,Nothing}
  
  function JuliaFunction(call_expr::Expr, return_type=nothing,
                         impl=nothing, doc=nothing)
    new(call_expr, return_type, impl, doc)
  end
end

@auto_hash_equals struct JuliaFunctionSig
  name::Symbol
  types::Vector{Expr0}
end

# Parsing Julia functions
#########################

""" Parse Julia expression that is (possibly) annotated with docstring.
"""
function parse_docstring(expr::Expr)::Tuple{Union{String,Nothing},Expr}
  expr = strip_lines(expr)
  if expr.head == :macrocall && (
      # XXX: It seems that the @doc macro can show up in two forms.
      expr.args[1] == GlobalRef(Core, Symbol("@doc")) ||
      expr.args[1] == Expr(:core, Symbol("@doc")))
    (expr.args[2], expr.args[3])
  else
    (nothing, expr)
  end
end

""" Parse Julia function definition into standardized form.
"""
function parse_function(expr::Expr)::JuliaFunction
  doc, expr = parse_docstring(expr)
  fun_expr, impl = @match expr begin
    Expr(:(=), args) => args
    Expr(:function, args) => args
    _ => throw(ParseError("Ill-formed function definition $expr"))
  end
  @match fun_expr begin
    (Expr(:(::), [Expr(:call, args), return_type]) => 
      JuliaFunction(Expr(:call, args...), return_type, impl, doc))
    (Expr(:call, args) =>
      JuliaFunction(Expr(:call, args...), nothing, impl, doc))
    _ => throw(ParseError("Ill-formed function header $fun_expr"))
  end
end

""" Parse signature of Julia function.
"""
function parse_function_sig(call_expr::Expr)::JuliaFunctionSig
  name, args = @match call_expr begin
    Expr(:call, [name::Symbol, Expr(:parameters, kw...), args...]) => (name, args)
    Expr(:call, [name::Symbol, args...]) => (name, args)
    _ => throw(ParseError("Ill-formed function signature $call_expr"))
  end
  types = map(args) do expr
    @match expr begin
      Expr(:(::), [_, typ]) => typ
      Expr(:(::), [typ]) => typ
      _ => :Any
    end
  end
  JuliaFunctionSig(name, types)
end
parse_function_sig(fun::JuliaFunction) = parse_function_sig(fun.call_expr)

""" Wrap Julia expression with docstring.
"""
function generate_docstring(expr::Expr, doc::Union{String,Nothing})::Expr
  if isnothing(doc)
    expr
  else
    Expr(:macrocall, GlobalRef(Core, Symbol("@doc")),
         LineNumberNode(0), doc, expr)
  end
end

""" Generate Julia expression for function definition.
"""
function generate_function(fun::JuliaFunction)::Expr
  head = if isnothing(fun.return_type)
    fun.call_expr
  else 
    Expr(:(::), fun.call_expr, fun.return_type)
  end
  body = if isnothing(fun.impl)
    Expr(:block)
  else
    # Wrap implementation inside block if not already.
    impl = fun.impl
    impl.head == :block ? impl : Expr(:block, impl)
  end
  expr = Expr(:function, head, body)
  generate_docstring(expr, fun.doc)
end

# Operations on Julia expressions
#################################

""" Append a Julia expression to a block expression.
"""
function append_expr!(block::Expr, expr)::Expr
  @assert block.head == :block
  @match expr begin
    Expr(:block, args) => append!(block.args, args)
    _ => push!(block.args, expr)
  end
  block
end

""" Concatenate two Julia expressions into a block expression.
"""
function concat_expr(expr1::Expr, expr2::Expr)::Expr
  @match (expr1, expr2) begin
    (Expr(:block, a1), Expr(:block, a2)) => Expr(:block, [a1; a2]...)
    (Expr(:block, a1), _) => Expr(:block, [a1; expr2]...)
    (_, Expr(:block, a2)) => Expr(:block, [expr1; a2]...)
    _ => Expr(:block, expr1, expr2)
  end
end

""" Replace symbols occurring anywhere in a Julia function (except the name).
"""
function replace_symbols(bindings::AbstractDict, f::JuliaFunction)::JuliaFunction
  JuliaFunction(
    Expr(f.call_expr.head, f.call_expr.args[1],
         (replace_symbols(bindings, a) for a in f.call_expr.args[2:end])...),
    isnothing(f.return_type) ? nothing : replace_symbols(bindings, f.return_type),
    isnothing(f.impl) ? nothing : replace_symbols(bindings, f.impl),
    f.doc
  )
end

""" Replace symbols occuring anywhere in a Julia expression.
"""
function replace_symbols(bindings::AbstractDict, expr)
  recurse(expr) = replace_symbols(bindings, expr)
  @match expr begin
    Expr(head, args) => Expr(head, map(recurse,args)...)
    sym::Symbol => get(bindings, sym, sym)
    _ => expr
  end
end

""" Remove all LineNumberNodes from a Julia expression.
"""
function strip_lines(expr::Expr; recurse::Bool=false)::Expr
  args = [ x for x in expr.args if !isa(x, LineNumberNode) ]
  if recurse
    args = [ isa(x, Expr) ? strip_lines(x; recurse=true) : x for x in args ]
  end
  Expr(expr.head, args...)
end

end
