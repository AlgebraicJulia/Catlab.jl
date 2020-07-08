""" Finite presentations of a model of a generalized algebraic theory (GAT).

We support two methods for defining models of a GAT: as Julia objects using the
`@instance` macro and as syntactic objects using the `@present` macro.
Instances are useful for casting generic data structures, such as matrices,
abstract tensor systems, and wiring diagrams, in categorical language.
Presentations define small categories by generators and relations and are useful
in applications like knowledge representation.
"""
module Present
export @present, Presentation, generator, generators, has_generator, equations,
  add_generator!, add_generators!, add_definition!, add_equation!

using Base.Meta: ParseError
using Compat
using Match

using ..Meta, ..Syntax
import ..GAT
import ..Syntax: parse_json_sexpr, to_json_sexpr

# Data types
############

struct Presentation{Theory,Name}
  syntax::Module
  generators::NamedTuple
  generator_name_index::Dict{Name,Pair{Symbol,Int}}
  equations::Vector{Pair}
end

function Presentation{Name}(syntax::Module) where Name
  Theory = syntax.theory()
  theory = GAT.theory(Theory)
  names = Tuple(type.name for type in theory.types)
  vectors = ((getfield(syntax, name){:generator})[] for name in names)
  Presentation{Theory,Name}(syntax, NamedTuple{names}(vectors),
                            Dict{Name,Pair{Symbol,Int}}(), Pair[])
end
Presentation(syntax::Module) = Presentation{Symbol}(syntax)

function Base.copy(pres::Presentation{T,Name}) where {T,Name}
  Presentation{T,Name}(pres.syntax, map(copy, pres.generators),
                       copy(pres.generator_name_index), copy(pres.equations))
end

# Presentation
##############

""" Get all generators of a presentation.
"""
generators(pres::Presentation) = collect(Iterators.flatten(pres.generators))
generators(pres::Presentation, type::Symbol) = pres.generators[type]
generators(pres::Presentation, type::Type) = generators(pres, nameof(type))

""" Retrieve generators by name.
"""
function generator(pres::Presentation, name)
  type, index = pres.generator_name_index[name]
  pres.generators[type][index]
end

""" Does the presentation contain a generator with the given name?
"""
function has_generator(pres::Presentation, name)
  haskey(pres.generator_name_index, name)
end

""" Add a generator to a presentation.
"""
function add_generator!(pres::Presentation, expr)
  name, type = first(expr), gat_typeof(expr)
  generators = pres.generators[type]
  if !isnothing(name)
    if haskey(pres.generator_name_index, name)
      error("Name $name already defined in presentation")
    end
    pres.generator_name_index[name] = type => length(generators)+1
  end
  push!(generators, expr)
  expr
end

""" Add iterable of generators to a presentation.
"""
function add_generators!(pres::Presentation, exprs)
  for expr in exprs
    add_generator!(pres, expr)
  end
end

""" Get all equations of a presentation.
"""
equations(pres::Presentation) = pres.equations

""" Add an equation between terms to a presentation.
"""
function add_equation!(pres::Presentation, lhs::GATExpr, rhs::GATExpr)
  push!(pres.equations, lhs => rhs)
end

""" Add a generator defined by an equation.
"""
function add_definition!(pres::Presentation, name::Symbol, rhs::GATExpr)
  generator = Syntax.generator_like(rhs, name)
  add_generator!(pres, generator)
  add_equation!(pres, generator, rhs)
  generator
end

# Presentation macro
####################

""" Define a presentation using a convenient syntax.
"""
macro present(head, body)
  name, pres = @match head begin
    Expr(:call, [name::Symbol, syntax_name::Symbol]) =>
      (name, :($(module_ref(:Presentation))($syntax_name)))
    Expr(:(<:), [name::Symbol, parent::Symbol]) => (name, :(copy($parent)))
    _ => throw(ParseError("Ill-formed presentation header $head"))
  end
  let_expr = Expr(:let, Expr(:block), translate_presentation(pres, body))
  esc(Expr(:(=), name, let_expr))
end

""" Translate a presentation in the DSL to a block of Julia code.
"""
function translate_presentation(pres::Expr0, body::Expr)::Expr
  @assert body.head == :block
  code = Expr(:block)
  append_expr!(code, :(_presentation = $pres))
  for expr in strip_lines(body).args
    append_expr!(code, translate_statement(expr))
  end
  append_expr!(code, :(_presentation))
  code
end

""" Translate a single statement in the presentation DSL to Julia code.
"""
function translate_statement(expr::Expr)::Expr
  @match expr begin
    Expr(:(::), [name::Symbol, type_expr]) =>
      translate_generator(name, type_expr)
    Expr(:(::), [type_expr]) =>
      translate_generator(nothing, type_expr)
    Expr(:(:=), [name::Symbol, def_expr]) =>
      translate_definition(name, def_expr)
    Expr(:call, [:(==), lhs, rhs]) => translate_equation(lhs, rhs)
    _ => throw(ParseError("Ill-formed presentation statement $expr"))
  end
end

""" Translate declaration of a generator.
"""
function translate_generator(name::Union{Symbol,Nothing}, type_expr)::Expr
  type_name, args = @match type_expr begin
    name::Symbol => (name, [])
    Expr(:call, [name::Symbol, args...]) => (name, args)
    _ => throw(ParseError("Ill-formed type expression $type_expr"))
  end
  gen_expr = Expr(:call, type_name,
                  isnothing(name) ? :nothing : QuoteNode(name), args...)
  Expr(:call, module_ref(:add_generator!), :_presentation,
       translate_expr(gen_expr))
end

""" Translate definition of generator in terms of other generators.
"""
function translate_definition(name::Symbol, def_expr)::Expr
  Expr(:call, module_ref(:add_definition!), :_presentation,
       QuoteNode(name), translate_expr(def_expr))
end

""" Translate declaration of equality between terms.
"""
function translate_equation(lhs, rhs)::Expr
  Expr(:call, module_ref(:add_equation!), :_presentation,
       translate_expr(lhs), translate_expr(rhs))
end

""" Translate GAT expression appearing in presentation.
"""
function translate_expr(expr)
  @match expr begin
    Expr(:call, [name::Symbol, args...]) =>
      Expr(:call, GlobalRef(Syntax, :invoke_term), :(_presentation.syntax),
           QuoteNode(name), map(translate_expr, args)...)
    name::Symbol =>
      Expr(:call, module_ref(:generator), :_presentation, QuoteNode(name))
    _ => expr
  end
end

module_ref(sym::Symbol) = GlobalRef(Present, sym)

# Serialization
###############

function to_json_sexpr(pres::Presentation, expr::GATExpr)
  to_json_sexpr(expr;
    by_reference = name -> has_generator(pres, name))
end

function parse_json_sexpr(pres::Presentation{Theory,Name},
                          syntax::Module, sexpr) where {Theory,Name}
  parse_json_sexpr(syntax, sexpr;
    symbols = Name == Symbol,
    parse_reference = name -> generator(pres, name))
end

end
