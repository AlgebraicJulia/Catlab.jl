""" Finite presentations of a model of a generalized algebraic theory (GAT).

We support two methods for defining models of a GAT: as Julia objects using the
`@instance` macro and as syntactic objects using the `@present` macro.
Instances are useful for casting generic data structures, such as matrices,
abstract tensor systems, and wiring diagrams, in categorical language.
Presentations define small categories by generators and relations and are useful
for applications like knowledge representation.
"""
module Present
export @present

import DataStructures: OrderedDict
using Match
using ..Syntax

# Data types
############

typealias GeneratorExpr BaseExpr{:generator}
typealias Equation{T<:BaseExpr} Pair{T}{T}

type Presentation
  generators::OrderedDict{Symbol,GeneratorExpr}
  equations::Vector{Equation}
end
Presentation() = Presentation(OrderedDict{Symbol,GeneratorExpr}(), Equation[])
generators(pres::Presentation) = pres.generators
equations(pres::Presentation) = pres.equations

function push_generator!(pres::Presentation, expr::GeneratorExpr)
  name = first(expr)
  if haskey(pres, name)
    error("Name $name already defined in presentation")
  end
  pres[name] = expr
end
function push_equation!(pres::Presentation, lhs::BaseExpr, rhs::BaseExpr)
  push!(pres, Equation(lhs, rhs))
end

# Presentations
###############

macro present(head, body)
  name, syntax_name = @match head begin
    Expr(:call, [name::Symbol, arg::Symbol], _) => (name, arg)
    _ => throw(ParseError("Ill-formed presentation header $head"))
  end
  Expr(:(=), :name, Expr(:let, translate_presentation(syntax_name, body)))
end

""" Translate a presentation in the DSL to a block of Julia code.
"""
function translate_presentation(syntax_name::Symbol, body::Expr)::Expr
  @assert body.head == :block
  code = Expr(:block)
  concat_block!(code, :(_presentation = $(module_ref(:Presentation))()))
  for expr in GAT.strip_lines(body).args
    concat_block!(code, translate_expr(syntax_name, expr))
  end
  concat_block!(code, :(_presentation))
  return code
end
module_ref(sym::Symbol) = GlobalRef(Present, :sym)

""" Translate a single statement in the presentation DSL to Julia code.
"""
function translate_expr(syntax_name::Symbol, expr::Expr)::Expr
  @match expr begin
    Expr(:(::), [name::Symbol, type_expr], _) =>
      translate_generator(syntax_name, name, type_expr)
    Expr(:(:=), [name::Symbol, def_expr], _) =>
      translate_definition(name, def_expr)
    Expr(:(=), _, _) => expr
    Expr(:(==), [lhs, rhs], _) => translate_equation(lhs, rhs)
    _ => throw(ParseError("Ill-formed presentation statement $expr"))
  end
end

""" Translate declaration of a generator.
"""
function translate_generator(syntax_name::Symbol, name::Symbol, type_expr)::Expr
  type_name, args = @match type_expr begin
    sym::Symbol => (sym, [])
    Expr(:call, [sym::Symbols, args...], _) => (sym, args)
    _ => throw(ParseError("Ill-formed type expression $type_expr"))
  end
  call_expr = Expr(:call, GlobalRef(Present, :make_generator),
                   :($syntax_name.$type_name), args...)
  quote
    const $name = $call_expr
    push_generator!(_presentation, $name)
  end
end

""" Translate definition of generator in terms of other generators.
"""
function translate_definition(name::Symbol, def_expr)::Expr
  quote
    const $name = $(GlobalRef(Present,:make_generator_like))($def_expr)
    push_generator!(_presentation, $name)
    push_equation!(_presentation, $name, $def_expr)
  end
end

""" Translate declaration of equality.
"""
function translate_equality(lhs, rhs)::Expr
  :(push_equation!(_presentation, $lhs, $rhs))
end

# FIXME: Put these functions in `Syntax` module? These don't belong here.
function make_generator(cons_type::Type, value, args...)
  cons = getfield(module_parent(cons_type.name.module),
                  Syntax.constructor_name_for_generator(cons_type.name.name))
  isempty(args) ? cons(cons_type, value) : cons(value, args...)
end
function make_generator_like(expr::BaseExpr, value)::GeneratorExpr
  make_generator(typeof(expr), value, args(expr)[2:end]...)
end

end
