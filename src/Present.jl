""" Finite presentations of a model of a generalized algebraic theory (GAT).

We support two methods for defining models of a GAT: as Julia objects using the
`@instance` macro and as syntactic objects using the `@present` macro.
Instances are useful for casting generic data structures, such as matrices,
abstract tensor systems, and wiring diagrams, in categorical language.
Presentations define small categories by generators and relations and are useful
for applications like knowledge representation.
"""
module Present
export @present, Presentation, Equation, generator, generators, has_generator,
  equations, add_generator!, add_generators!, add_definition!, add_equation!

import DataStructures: OrderedSet
using Match
using ..Meta, ..Syntax

# Data types
############

const GenExpr = BaseExpr{:generator}
const Equation = Pair{<:BaseExpr}{<:BaseExpr}

mutable struct Presentation{T}
  generators::OrderedSet{GenExpr}
  generators_by_name::Dict{T,GenExpr}
  equations::OrderedSet{Equation}
end
Presentation(T::Type) = Presentation{T}(
  OrderedSet{GenExpr}(), Dict{T,GenExpr}(), OrderedSet{Equation}())
Presentation() = Presentation(Symbol)

# Presentation
##############

""" Get all generators of a presentation.
"""
function generators(pres::Presentation)::Vector
  collect(pres.generators)
end
function generators(pres::Presentation, typ::Type)::Vector
  filter(x -> isa(x,typ), collect(pres.generators))
end

""" Retrieve a generator by name.
"""
function generator{T}(pres::Presentation{T}, name)
  pres.generators_by_name[convert(T, name)]
end

""" Does the presentation contain a generator with the given name?
"""
function has_generator{T}(pres::Presentation{T}, name)
  haskey(pres.generators_by_name, convert(T, name))
end

""" Add a generator to a presentation.
"""
function add_generator!{T}(pres::Presentation{T}, expr::GenExpr)
  name = first(expr)
  if name != nothing
    name = convert(T, name)
    if haskey(pres.generators_by_name, name)
      error("Name $name already defined in presentation")
    end
    pres.generators_by_name[name] = expr
  end
  push!(pres.generators, expr)
  return expr
end

""" Add multiple generators to a presentation.
"""
function add_generators!(pres::Presentation, exprs)
  for expr in exprs
    add_generator!(pres, expr)
  end
end

""" Get all equations of a presentation.
"""
function equations(pres::Presentation)::Vector
  collect(pres.equations)
end

""" Add an equation between terms to a presentation.
"""
function add_equation!(pres::Presentation, lhs::BaseExpr, rhs::BaseExpr)
  push!(pres.equations, lhs => rhs)
end

""" Add a generator defined by an equation.
"""
function add_definition!(pres::Presentation, name::Symbol, rhs::BaseExpr)
  generator = Syntax.generator_like(rhs, name)
  add_generator!(pres, generator)
  add_equation!(pres, generator, rhs)
  return generator
end

# Presentation macro
####################

""" Define a presentation using a convenient syntax.
"""
macro present(head, body)
  name, syntax_name = @match head begin
    Expr(:call, [name::Symbol, arg::Symbol], _) => (name, arg)
    _ => throw(ParseError("Ill-formed presentation header $head"))
  end
  code = Expr(:(=), name, Expr(:let, translate_presentation(syntax_name, body)))
  esc(code)
end

""" Translate a presentation in the DSL to a block of Julia code.
"""
function translate_presentation(syntax_name::Symbol, body::Expr)::Expr
  @assert body.head == :block
  code = Expr(:block)
  append_expr!(code, :(_presentation = $(module_ref(:Presentation))()))
  for expr in strip_lines(body).args
    append_expr!(code, translate_expr(syntax_name, expr))
  end
  append_expr!(code, :(_presentation))
  return code
end

""" Translate a single statement in the presentation DSL to Julia code.
"""
function translate_expr(syntax_name::Symbol, expr::Expr)::Expr
  @match expr begin
    Expr(:(::), [name::Symbol, type_expr], _) =>
      translate_generator(syntax_name, Nullable(name), type_expr)
    Expr(:(::), [type_expr], _) =>
      translate_generator(syntax_name, Nullable{Symbol}(), type_expr)
    Expr(:(:=), [name::Symbol, def_expr], _) =>
      translate_definition(name, def_expr)
    Expr(:(=), _, _) => expr
    Expr(:call, [:(==), lhs, rhs], _) => translate_equation(lhs, rhs)
    _ => throw(ParseError("Ill-formed presentation statement $expr"))
  end
end

""" Translate declaration of a generator.
"""
function translate_generator(syntax_name::Symbol, name::Nullable{Symbol}, type_expr)::Expr
  type_name, args = @match type_expr begin
    sym::Symbol => (sym, [])
    Expr(:call, [sym::Symbol, args...], _) => (sym, args)
    _ => throw(ParseError("Ill-formed type expression $type_expr"))
  end
  call_expr = Expr(
    :call, module_ref(:add_generator!),
    :_presentation,
    Expr(:call, GlobalRef(Syntax, :invoke_term),
         syntax_name,
         QuoteNode(type_name),
         isnull(name) ? :nothing : QuoteNode(get(name)),
         args...))
  isnull(name) ? call_expr : :(const $(get(name)) = $call_expr)
end

""" Translate definition of generator in terms of other generators.
"""
function translate_definition(name::Symbol, def_expr)::Expr
  call_expr = Expr(:call, module_ref(:add_definition!), :_presentation,
                   QuoteNode(name), def_expr)
  :(const $name = $call_expr)
end

""" Translate declaration of equality between terms.
"""
function translate_equation(lhs, rhs)::Expr
  Expr(:call, module_ref(:add_equation!), :_presentation, lhs, rhs)
end

module_ref(sym::Symbol) = GlobalRef(Present, sym)

end
