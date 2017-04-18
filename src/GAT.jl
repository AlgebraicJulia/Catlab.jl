""" Generalized algebraic theories (GATs) in Julia.

GATs generalize (multisorted) algebraic theories by incorporating a fragment of
dependent type theory. They allow type and term constructors to be partially
defined. GATs provide a convenient formal syntax for categorical structures.

At present, this module only supports defining the *signature* of a GAT. In the
future we may allow *axioms* to be expressed as well. Regardless, we will
persist in calling this module "GAT". Signatures are defined using the
`@signature` macro.

There are two useful things to do with a GAT signature:

1. Define *instances* of the signature (models of the theory) using the
  `@instance` macro
2. Define *syntax* systems using the `@syntax` macro (see `Syntax` module)

References:

- (Cartmell, 1986, "Generalized algebraic theories and contextual categoies")
- (Pitts, 1995, "Categorical logic", Sec 6: "Dependent types")
"""
module GAT
export @signature, @instance

using AutoHashEquals
import DataStructures: OrderedDict
using Match

# Data types
############

""" Base type for method stubs in GAT signature.
"""
abstract Stub

typealias Expr0 Union{Symbol,Expr}
typealias Context OrderedDict{Symbol,Expr0}

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

@auto_hash_equals immutable TypeConstructor
  name::Symbol
  params::Vector{Symbol}
  context::Context
end

@auto_hash_equals immutable TermConstructor
  name::Symbol
  params::Vector{Symbol}
  typ::Expr0
  context::Context
end

""" Signature for a generalized algebraic theory (GAT).
"""
@auto_hash_equals immutable Signature
  types::Vector{TypeConstructor}
  terms::Vector{TermConstructor}
end

immutable SignatureBinding
  name::Symbol
  params::Vector{Symbol}
end

immutable SignatureHead
  main::SignatureBinding
  base::Vector{SignatureBinding}
  SignatureHead(main, base=[]) = new(main, base)
end

""" Typeclass = GAT signature + Julia-specific content.
"""
immutable Typeclass
  name::Symbol
  type_params::Vector{Symbol}
  signature::Signature
  functions::Vector{JuliaFunction}
end

# Julia expressions
###################

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
function gen_function(fun::JuliaFunction)::Expr
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

""" Add a type-valued first argument to a Julia function signature.

We need this to avoid ambiguity in method dispatch when a term constructor has
no arguments (e.g., `munit()`) or more generally has no arguments that are types
in the signature (e.g., object generators in a category).

The fundamental reason why these cases must be treated specially is that Julia
does not (yet?) support
[dispatching on return type](https://github.com/JuliaLang/julia/issues/19206).
"""
function add_type_dispatch(call_expr::Expr, type_expr::Expr0)::Expr
  @match call_expr begin
    (Expr(:call, [name, args...], _) =>
      Expr(:call, name, :(::Type{$type_expr}), args...))
    _ => throw(ParseError("Ill-formed call expression $call_expr"))
  end
end

""" Replace types in signature of Julia function.
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

""" Replace symbols (occuring anywhere) in a Julia expression.
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
  
# GAT expressions
#################

""" Parse a raw expression in a GAT.

A "raw expression" is a just composition of function and constant symbols.
"""
function parse_raw_expr(expr)
  @match expr begin
    Expr(:call, args, _) => map(parse_raw_expr, args)
    head::Symbol => nothing
    _ => throw(ParseError("Ill-formed raw expression $expr"))
  end
  expr # Return the expression unmodified. This function just checks syntax.
end

""" Parse context for term or type in a GAT.
"""
function parse_context(expr::Expr)::Context
  @assert expr.head == :tuple
  context = Context()
  for arg in expr.args
    name, typ = @match arg begin
      Expr(:(::), [name::Symbol, typ], _) => (name, parse_raw_expr(typ))
      _ => throw(ParseError("Ill-formed context expression $expr"))
    end
    push_context!(context, name, typ)
  end
  return context
end
function push_context!(context, name, expr)
  if haskey(context, name)
    throw(ParseError("Name $name already defined"))
  end
  context[name] = expr
end

""" Parse type or term constructor in a GAT.
"""
function parse_constructor(expr::Expr)::Union{TypeConstructor,TermConstructor}
  # Context is optional.
  cons_expr, context = @match expr begin
    Expr(:call, [:<=, inner, context], _) => (inner, parse_context(context))
    _ => (expr, Context())
  end
  
  # Allow abbreviated syntax where tail of context is included in parameters.
  function parse_params(params)::Vector{Symbol}
    [ @match param begin
        Expr(:(::), [name::Symbol, typ], _) => begin
          push_context!(context, name, parse_raw_expr(typ))
          name
        end
        name::Symbol => name
        _ => throw(ParseError("Ill-formed type/term parameter $param"))
      end for param in params ]
  end
  
  @match cons_expr begin
    (Expr(:(::), [name::Symbol, :TYPE], _)
      => TypeConstructor(name, [], context))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...], _), :TYPE], _)
      => TypeConstructor(name, parse_params(params), context))
    (Expr(:(::), [Expr(:call, [name::Symbol, params...], _), typ], _)
      => TermConstructor(name, parse_params(params), parse_raw_expr(typ), context))
    _ => throw(ParseError("Ill-formed type/term constructor $cons_expr"))
  end
end

""" Generate abstract type definition from a GAT type constructor.
"""
function gen_abstract_type(cons::TypeConstructor)::Expr
  stub_name = GlobalRef(GAT, :Stub)
  :(abstract $(cons.name) <: $stub_name)
end

""" Replace names of type constructors in a GAT.
"""
function replace_types(bindings::Dict, sig::Signature)::Signature
  Signature([ replace_types(bindings, t) for t in sig.types ],
            [ replace_types(bindings, t) for t in sig.terms ])
end
function replace_types(bindings::Dict, cons::TypeConstructor)::TypeConstructor
  TypeConstructor(replace_symbols(bindings, cons.name),
                  cons.params,
                  replace_types(bindings, cons.context))
end
function replace_types(bindings::Dict, cons::TermConstructor)::TermConstructor
  TermConstructor(cons.name, cons.params,
                  replace_symbols(bindings, cons.typ),
                  replace_types(bindings, cons.context))
end
function replace_types(bindings::Dict, context::Context)::Context
  GAT.Context(((name => @match expr begin
    (Expr(:call, [sym::Symbol, args...], _) => 
      Expr(:call, replace_symbols(bindings, sym), args...))
    sym::Symbol => replace_symbols(bindings, sym)
  end) for (name, expr) in context))
end

""" Remove type parameters from dependent type.
"""
function strip_type(expr)::Symbol
  @match expr begin
    Expr(:call, [head::Symbol, args...], _) => head
    sym::Symbol => sym
  end
end

# Signatures
############

""" Define a signature of a generalized algebraic theory (GAT).

Three kinds of things can go in the signature body:

1. Type constructors, indicated by the special type `TYPE`, e.g.
   `Hom(X::Ob,Y::Ob)::TYPE`
2. Term constructors, e.g.,
   `id(X::Ob)::Hom(X,X)`
3. Julia functions operating on the term constructors to provide additional
   functionality

A signature can extend existing signatures (at present only one).
"""
macro signature(head, body)
  # Parse signature header.
  head = parse_signature_head(head)
  @assert length(head.base) <= 1 "Multiple signature extension not supported"
  if length(head.base) == 1
    base_name, base_params = head.base[1].name, head.base[1].params
    @assert all(p in head.main.params for p in base_params)
  else 
    base_name, base_params = nothing, []
  end
    
  # Parse signature body: GAT types/terms and extra Julia functions.
  types, terms, functions = parse_signature_body(body)
  signature = Signature(types, terms)
  class = Typeclass(head.main.name, head.main.params, signature, functions)
  
  # We must generate and evaluate the code at *run time* because the base
  # signature, if specified, is not available at *parse time*.
  expr = :(signature_code($class, $(esc(base_name)), $base_params))
  Expr(:block,
    Expr(:call, esc(:eval), expr),
    :(Core.@__doc__ $(esc(head.main.name))))
end
function signature_code(main_class, base_mod, base_params)
  # Add types/terms/functions from base class, if provided.
  if base_mod == nothing
    class = main_class
  else
    base_class = base_mod.class()
    bindings = Dict(zip(base_class.type_params, base_params))
    main_sig = main_class.signature
    base_sig = replace_types(bindings, base_class.signature)
    sig = Signature([base_sig.types; main_sig.types],
                    [base_sig.terms; main_sig.terms])
    functions = [ [ replace_symbols(bindings, f) for f in base_class.functions ];
                  main_class.functions ]
    class = Typeclass(main_class.name, main_class.type_params, sig, functions)
  end
  signature = class.signature
  
  # Generate module with stub types.
  mod = Expr(:module, true, class.name, 
    Expr(:block, [
      Expr(:export, [cons.name for cons in signature.types]...);
      map(gen_abstract_type, signature.types);      
      :(class() = $(class));
    ]...))
  
  # Generate method stubs.
  # (We put them outside the module, so the stub type names must be qualified.)
  bindings = Dict(cons.name => Expr(:(.), class.name, QuoteNode(cons.name))
                  for cons in signature.types)
  fns = interface(class)
  toplevel = [ gen_function(replace_symbols(bindings, f)) for f in fns ]
  
  # Modules must be at top level:
  # https://github.com/JuliaLang/julia/issues/21009
  Expr(:toplevel, mod, toplevel...)
end

function parse_signature_head(expr::Expr)::SignatureHead
  parse = parse_signature_binding
  @match expr begin
    (Expr(:(=>), [Expr(:tuple, bases, _), main], _)
      => SignatureHead(parse(main), map(parse, bases)))
    Expr(:(=>), [base, main], _) => SignatureHead(parse(main), [parse(base)])
    _ => SignatureHead(parse(expr))
  end
end

function parse_signature_binding(expr::Expr)::SignatureBinding
  @match expr begin
    Expr(:call, [name::Symbol, params...], _) => SignatureBinding(name, params)
    _ => throw(ParseError("Ill-formed signature binding $expr"))
  end
end

""" Parse the body of a GAT signature declaration.
"""
function parse_signature_body(expr::Expr)
  @assert expr.head == :block
  types, terms, funs = OrderedDict(), [], []
  for elem in strip_lines(expr).args
    if elem.head in (:(::), :call)
      cons = parse_constructor(elem)
      if isa(cons, TypeConstructor)
        if haskey(types, cons.name)
          throw(ParseError("Duplicate type constructor $elem"))
        else
          types[cons.name] = cons end
      else
        push!(terms, cons) end
    elseif elem.head in (:(=), :function)
      push!(funs, parse_function(elem))
    else
      throw(ParseError("Ill-formed signature element $elem"))
    end
  end
  return (collect(values(types)), terms, funs)
end

""" Julia functions for type parameter accessors.
"""
function accessors(sig::Signature)::Vector{JuliaFunction}
  vcat(map(accessors, sig.types)...)
end
function accessors(cons::TypeConstructor)::Vector{JuliaFunction}
  [ JuliaFunction(Expr(:call, param, Expr(:(::), cons.name)),
                  strip_type(cons.context[param]))
    for param in cons.params ]
end

""" Julia functions for term constructors of GAT.
"""
function constructors(sig::Signature)::Vector{JuliaFunction}
  [ constructor(cons, sig) for cons in sig.terms ]
end
function constructor(cons::TermConstructor, sig::Signature)::JuliaFunction
  arg_names = cons.params
  arg_types = [ strip_type(cons.context[name]) for name in arg_names ]
  args = [ Expr(:(::), name, typ) for (name,typ) in zip(arg_names, arg_types) ]
  return_type = strip_type(cons.typ)
  
  call_expr = Expr(:call, cons.name, args...)
  if all(!has_type(sig, typ) for typ in arg_types)
    call_expr = add_type_dispatch(call_expr, return_type)
  end
  JuliaFunction(call_expr, return_type)
end

""" Complete set of Julia functions for a type class.
"""
function interface(class::Typeclass)::Vector{JuliaFunction}
  [ accessors(class.signature);
    constructors(class.signature);
    class.functions ]
end

""" Get type constructor by name.

Unlike term constructors, type constructors cannot be overloaded, so there is at
most one type constructor with a given name.
"""
function get_type(sig::Signature, name::Symbol)::TypeConstructor
  indices = find(cons -> cons.name == name, sig.types)
  @assert length(indices) == 1
  sig.types[indices[1]]
end
function has_type(sig::Signature, name::Symbol)::Bool
  findfirst(cons -> cons.name == name, sig.types) != 0
end

# GAT expressions in a signature
################################

""" Expand context variables that occur implicitly in an expression.

Reference: (Cartmell, 1986, Sec 10: 'Informal syntax').
"""
function expand_in_context(expr, params::Vector{Symbol},
                           context::Context, sig::Signature)
  @match expr begin
    Expr(:call, [name::Symbol, args...], _) => begin
      expanded = [expand_in_context(e, params, context, sig) for e in args]
      Expr(:call, name, expanded...)
    end
    name::Symbol => begin
      if name in params
        name
      elseif haskey(context, name)
        expand_symbol_in_context(name, params, context, sig)
      else
        error("Name $name missing from context $context")
      end
    end
    _ => throw(ParseError("Ill-formed raw expression $expr"))
  end
end
function expand_symbol_in_context(sym::Symbol, params::Vector{Symbol},
                                  context::Context, sig::Signature)
  # This code expands symbols that occur as direct arguments to type
  # constructors. If there are term constructors in between, it does not work:
  # indeed, it cannot work in general because the term constructors are not
  # necessarily injective. For example, we can expand :X in
  #   (:X => :Ob, :f => :(Hom(X)))
  # but not in
  #   (:X => :Ob, :Y => :Ob, :f => :(Hom(otimes(X,Y))))
  names = collect(keys(context))
  start = findfirst(names .== sym)
  for name in names[start+1:end]
    expr = context[name]
    if isa(expr, Expr) && expr.head == :call && sym in expr.args[2:end]
      cons = get_type(sig, expr.args[1])
      accessor = cons.params[findfirst(expr.args[2:end] .== sym)]
      expanded = Expr(:call, accessor, name)
      return expand_in_context(expanded, params, context, sig)
    end
  end
  error("Name $sym does not occur explicitly among $params in context $context")
end

""" Expand context variables that occur implicitly in the type expression 
of a term constructor.
"""
function expand_term_type(cons::TermConstructor, sig::Signature)
  isa(cons.typ, Symbol) ? cons.typ :
    expand_in_context(cons.typ, cons.params, cons.context, sig)
end

""" Implicit equations defined by a context.

This function allows a generalized algebraic theory (GAT) to be expressed as
an essentially algebraic theory, i.e., as partial functions whose domains are
defined by equations.

References:
 - (Cartmell, 1986, Sec 6: "Essentially algebraic theories and categories with 
    finite limits")
 - (Freyd, 1972, "Aspects of topoi")
"""
function equations(context::Context, sig::Signature)::Vector{Pair}
  # The same restrictions as `expand_symbol_in_context` apply here.
  eqs = Pair[]
  names = collect(keys(context))
  for (start, var) in enumerate(names)
    for name in names[start+1:end]
      expr = context[name]
      if isa(expr, Symbol) && !has_type(sig, expr)
        # If the constructor is a symbol and there isn't a matching type in
        # the signature, assume it's a Julia type. For now, these are
        # completely ignored by the syntax system.
        continue
      end
      expr = isa(expr, Symbol) ? Expr(:call, expr) : expr
      cons = get_type(sig, expr.args[1])
      accessors = cons.params[find(expr.args[2:end] .== var)]
      append!(eqs, (Expr(:call, a, name) => var for a in accessors))
    end
  end
  eqs
end

""" Implicit equations defined by context, allowing for implicit variables.
"""
function equations(params::Vector{Symbol}, context::Context,
                   sig::Signature)::Vector{Pair}
  eqs = ((expand_in_context(lhs, params, context, sig) =>
          expand_in_context(rhs, params, context, sig))
         for (lhs, rhs) in equations(context, sig))
  # Remove tautologies (expr == expr) resulting from expansions.
  # FIXME: Should we worry about redundancies from the symmetry of equality,
  # i.e., (expr1 == expr2) && (expr2 == expr1)?
  collect(filter(eq -> eq.first != eq.second, eqs))
end

""" Implicit equations for term constructor.
"""
function equations(cons::TermConstructor, sig::Signature)::Vector{Pair}
  equations(cons.params, cons.context, sig)
end

# Instances
###########

""" Define an *instance* of a generalized algebraic theory (GAT).

These are perfectly analagous to instances of a type class in Haskell. See also
the Typeclass.jl library for Julia.
"""
macro instance(head, body)
  # Parse the instance definition.
  head = parse_signature_binding(head)
  functions = parse_instance_body(body)
  
  # We must generate and evaluate the code at *run time* because the signature
  # module is not defined at *parse time*.
  # Also, we "throw away" any docstring.
  # FIXME: Is there a better place to put the docstring?
  expr = :(instance_code($(esc(head.name)), $(esc(head.params)), $functions))
  Expr(:block,
    Expr(:call, esc(:eval), expr),
    :(Core.@__doc__ abstract $(esc(gensym(:instance_doc))))) # /dev/null
end
function instance_code(mod, instance_types, instance_fns)
  code = Expr(:block)
  class = mod.class()
  bindings = Dict(zip(class.type_params, instance_types))
  bound_fns = [ replace_symbols(bindings, f) for f in interface(class) ]
  bound_fns = OrderedDict(parse_function_sig(f) => f for f in bound_fns)
  instance_fns = Dict(parse_function_sig(f) => f for f in instance_fns)
  for (sig, f) in bound_fns
    if haskey(instance_fns, sig)
      f_impl = instance_fns[sig]
    elseif !isnull(f.impl)
      f_impl = f
    else
      error("Method $(f.call_expr) not implemented in $(class.name) instance")
    end
    push!(code.args, gen_function(f_impl))
  end
  return code
end

""" Parse the body of a GAT instance definition.
"""
function parse_instance_body(expr::Expr)::Vector{JuliaFunction}
  @match strip_lines(expr) begin
    Expr(:block, args, _) => map(parse_function, args)
    _ => throw(ParseEror("Ill-formed instance definition"))
  end  
end

end
