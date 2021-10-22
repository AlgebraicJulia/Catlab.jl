""" DSLs for defining categories, diagrams, and related structures.

Here "diagram" means diagram in the standard category-theoretic sense, not
string diagram or wiring diagram. DSLs for constructing wiring diagrams are
provided by other submodules.
"""
module DiagrammaticPrograms
export @graph, @category, @diagram, @migration

using Base.Iterators: repeated
using MLStyle: @match
using StaticArrays: SVector

using ...Present, ...Graphs, ...CategoricalAlgebra
using ...Theories: munit
using ...Graphs.BasicGraphs: TheoryGraph

# Data types
############

@present TheoryNamedGraph <: TheoryGraph begin
  Name::AttrType
  vname::Attr(V, Name)
  ename::Attr(E, Name)
end

""" Default graph type for [`@category`](@ref) macro and related macros.
"""
@acset_type NamedGraph(TheoryNamedGraph, index=[:src,:tgt],
                       unique_index=[:vname,:ename]) <: AbstractGraph

@present TheoryMaybeNamedGraph <: TheoryGraph begin
  VName::AttrType
  EName::AttrType
  vname::Attr(V, VName)
  ename::Attr(E, EName)
end

@acset_type _MaybeNamedGraph(TheoryMaybeNamedGraph, index=[:src,:tgt],
                             unique_index=[:vname]) <: AbstractGraph

""" Default graph type for [`@graph`](@ref) macro.

Vertex names are uniquely indexed and edge names are optional and unindexed.
"""
const MaybeNamedGraph{Name} = _MaybeNamedGraph{Name,Union{Nothing,Name}}

vertex_named(g, name) = incident(g, name, :vname)
edge_named(g, name)= incident(g, name, :ename)

# Graphs
########

""" Construct a graph in a simple, declarative style.

The syntax is reminiscent of Graphviz. Each line a declares a vertex or set of
vertices, or an edge. For example, the following defines a directed triangle:

```julia
@graph begin
  v0, v1, v2
  fst: v0 → v1
  snd: v1 → v2
  comp: v0 → v2
end
```

Vertices in the graph must be uniquely named, whereas edges names are optional
and need not be unique.
"""
macro graph(graph_type, body)
  :(parse_graph($(esc(graph_type)), $(Meta.quot(body))))
end
macro graph(body)
  :(parse_graph(MaybeNamedGraph{Symbol}, $(Meta.quot(body))))
end

function parse_graph(G::Type, body::Expr; preprocess::Bool=true)
  g = G()
  if preprocess
    body = preprocess_expr!(body)
  end
  for expr in body.args
    @match expr begin
      # v
      v::Symbol => add_vertex!(g, vname=v)
      # u, v, ...
      Expr(:tuple, vs...) => add_vertices!(g, length(vs), vname=vs)
      # u → v
      Expr(:call, :(→), u::Symbol, v::Symbol) => parse_edge!(g, u, v)
      # e : u → v
      Expr(:call, :(:), e::Symbol, Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        parse_edge!(g, u, v, ename=e)
      # (e, f, ...) : u → v
      Expr(:call, (:), Expr(:tuple, es...), Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        for e in es; parse_edge!(g, u, v, ename=e) end
      _ => error("@graph macro cannot parse line: $expr")
    end
  end
  return g
end

function parse_edge!(g, s::Symbol, t::Symbol;
                     ename::Union{Symbol,Nothing}=nothing)
  e = add_edge!(g, vertex_named(g, s), vertex_named(g, t))
  if has_subpart(g, :ename)
    g[e,:ename] = ename
  end
  return e
end

function preprocess_expr!(expr)
  expr |> Base.remove_linenums! |> reparse_arrows
end
function reparse_arrows(expr)
  # `f : x → y` is parsed by Julia as `(f : x) → y`, not `f : (x → y)`.
  @match expr begin
    Expr(:call, :(→), Expr(:call, :(:), f, x), y) =>
      Expr(:call, :(:), f, Expr(:call, :(→), x, y))
    Expr(head, args...) => Expr(head, (reparse_arrows(arg) for arg in args)...)
    _ => expr
  end
end

# Categories
############

""" Present a category by generators and relations.

The result is a finitely presented category (`FinCat`) represented by a graph,
possibly with path equations. For example, the simplex category truncated to one
dimension is:

```julia
@category begin
  V, E
  (δ₀, δ₁): V → E
  σ₀: E → V

  σ₀ ∘ δ₀ == id(V)
  σ₀ ∘ δ₁ == id(V)
end
```

The objects and morphisms must be uniquely named.
"""
macro category(body)
  parse_category(NamedGraph{Symbol}, body)
end

function parse_category(G::Type, body::Expr; preprocess::Bool=true)
  g, eqs = G(), Pair[]
  if preprocess
    body = preprocess_expr!(body)
  end
  for expr in body.args
    @match expr begin
      # v
      v::Symbol => add_vertex!(g, vname=v)
      # u, v, ...
      Expr(:tuple, vs...) => add_vertices!(g, length(vs), vname=vs)
      # e : u → v
      Expr(:call, :(:), e::Symbol, Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        parse_edge!(g, u, v, ename=e)
      # (e, f, ...) : u → v
      Expr(:call, (:), Expr(:tuple, es...), Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        for e in es; parse_edge!(g, u, v, ename=e) end
      # f == g
      Expr(:call, :(==), lhs, rhs) => push!(eqs, parse_path_equation(g, lhs, rhs))
      _ => error("@category macro cannot parse line: $expr")
    end
  end
  isempty(eqs) ? FinCat(g) : FinCat(g, eqs)
end

""" Parse an equation between paths in a named graph.
"""
parse_path_equation(g, lhs, rhs) = parse_path(g, lhs) => parse_path(g, rhs)

""" Parse a path in a named graph.
"""
function parse_path(g, expr)
  function parse(expr)
    @match expr begin
      Expr(:call, :compose, args...) => mapreduce(parse, vcat, args)
      Expr(:call, :(⋅), f, g) ||
      Expr(:call, :(⨟), f, g) => vcat(parse(f), parse(g))
      Expr(:call, :(∘), f, g) => vcat(parse(g), parse(f))
      Expr(:call, :id, x) => empty(Path, g, vertex_named(g, x))
      f::Symbol => Path(g, edge_named(g, f))
      _ => error("Invalid morphism expression $expr")
    end
  end
  parse(expr)
end

# Diagrams
##########

""" Present a diagram in a given category.

Recall that a *diagram* in a category ``C`` is a functor ``F: J → C`` from a
small category ``J`` into ``C``. Given the category ``C``, this macro presents a
diagram in ``C``, i.e., constructs a finitely presented indexing category ``J``
together with a functor ``F: J → C``. This method of simultaneous definition is
often more convenient than defining ``J`` and ``F`` separately.

For example, the following diagram specifies the paths of length two in a graph:

```julia
@diagram FinCat(TheoryGraph) begin
  v::V
  (e1, e2)::E
  (t: e1 → v)::tgt
  (s: e2 → v)::src
end
```
"""
macro diagram(category, body)
  :(parse_diagram($(Meta.quot(body)), $(esc(category))))
end

function parse_diagram(body::Expr, C::Cat; preprocess::Bool=true)
  g, eqs = NamedGraph{Symbol}(), Pair[]
  F_ob, F_hom = [], []
  if preprocess
    body = preprocess_expr!(body)
  end
  for expr in body.args
    @match expr begin
      # x => X
      Expr(:call, :(=>), x::Symbol, X::Symbol) ||
      # x::X
      Expr(:(::), x::Symbol, X::Symbol) => begin
        add_vertex!(g, vname=x)
        push!(F_ob, X)
      end
      # (x, y, ...) => X
      Expr(:call, :(=>), Expr(:tuple, xs...), X::Symbol) ||
      # (x, y, ...)::X
      Expr(:(::), Expr(:tuple, xs...), X::Symbol) => begin
        add_vertices!(g, length(xs), vname=xs)
        append!(F_ob, repeated(X, length(xs)))
      end
      # (e: x → y) => f
      Expr(:call, :(=>), Expr(:call, :(:), e::Symbol,
                              Expr(:call, :(→), x::Symbol, y::Symbol)), f) ||
      # (e: x → y)::f
      Expr(:(::), Expr(:call, :(:), e::Symbol,
                       Expr(:call, :(→), x::Symbol, y::Symbol)), f) => begin
        parse_edge!(g, x, y, ename=e)
        push!(F_hom, parse_hom(C, f))
      end
      # f == g
      Expr(:call, :(==), lhs, rhs) => push!(eqs, parse_path_equation(g, lhs, rhs))
      _ => error("@diagram macro cannot parse line: $expr")
    end
  end
  J = isempty(eqs) ? FinCat(g) : FinCat(g, eqs)
  F = FinDomFunctor(F_ob, F_hom, J, C)
  is_functorial(F, check_equations=false) ||
    error("@diagram macro defined diagram that is not functorial: $F")
  return F
end
function parse_diagram(body::Expr, pres::Presentation; kw...)
  parse_diagram(body, FinCat(pres); kw...)
end

""" Parse expression for morphism in a category.
"""
function parse_hom(C::Cat, expr)
  function parse(expr)
    @match expr begin
      Expr(:call, :compose, args...) =>
        mapreduce(parse, (fs...) -> compose(C, fs...), args)
      Expr(:call, :(⋅), f, g) ||
      Expr(:call, :(⨟), f, g) => compose(C, parse(f), parse(g))
      Expr(:call, :(∘), f, g) => compose(C, parse(g), parse(f))
      Expr(:call, :id, x) => id(C, ob(C, x))
      f::Symbol => hom(C, f)
      _ => error("Invalid morphism expression $expr")
    end
  end
  parse(expr)
end

# Data migrations
#################

""" Define a data migration query.

This macro provides a DSL to specify a data migration query from a ``C``-set to
a ``D``-set for arbitrary schemas ``C`` and ``D``.
"""
macro migration(src_schema, body)
  :(parse_migration($(Meta.quot(body)), $(esc(src_schema))))
end
#macro migration(tgt_schema, src_schema, body)
#  :(parse_migration($(Meta.quot(body)), $(esc(src_schema)), $(esc(tgt_schema))))
#end

function parse_migration(body::Expr, src_schema::Presentation;
                         preprocess::Bool=true)
  src_schema = FinCat(src_schema)
  tgt_graph, tgt_eqs = NamedGraph{Symbol}(), Pair[]
  F_ob, F_hom = Union{Some,Diagram}[], Union{Some,DiagramHom}[]
  if preprocess
    body = preprocess_expr!(body)
  end
  for expr in body.args
    @match expr begin
      # x => y
      Expr(:call, :(=>), x::Symbol, y::Symbol) => begin
        add_vertex!(tgt_graph, vname=x)
        push!(F_ob, Some(y))
      end
      # x => @limit ...
      # x => @join ...
      Expr(:call, :(=>), x::Symbol, Expr(:macrocall, form, args...)) &&
          if form ∈ (Symbol("@limit"), Symbol("@join")) end => begin
        D = parse_diagram(last(args), src_schema, preprocess=false)
        add_vertex!(tgt_graph, vname=x)
        push!(F_ob, Diagram{op}(D))
      end
      # (f: x → x′) => ...
      Expr(:call, :(=>), Expr(:call, :(:), f::Symbol,
                              Expr(:call, :(→), x::Symbol, x′::Symbol)), block) => begin
        e = parse_edge!(tgt_graph, x, x′, ename=f)
        v, v′ = src(tgt_graph, e), tgt(tgt_graph, e)
        push!(F_hom, parse_diagram_hom(src_schema, block, F_ob[v], F_ob[v′]))
      end
      # f == g
      Expr(:call, :(==), lhs, rhs) => push!(tgt_eqs, parse_equation(g, lhs, rhs))
      _ => error("@migration macro cannot parse line: $expr")
    end
  end
  F_ob = map(x -> coerce_diagram(src_schema, something(x)), F_ob)
  F_hom = map(f -> coerce_diagram_hom(src_schema, something(f)), F_hom)
  J = isempty(tgt_eqs) ? FinCat(tgt_graph) : FinCat(tgt_graph, tgt_eqs)
  F = FinDomFunctor(F_ob, F_hom, J)
  is_functorial(F, check_equations=false) ||
    error("@migration macor defined diagram that is not functorial: $F")
  return F
end

coerce_diagram(C::Cat, d::Diagram{op}) = d
coerce_diagram(C::Cat, c) = munit(Diagram{op}, C, c)
coerce_diagram_hom(C::Cat, f::DiagramHom{op}) = f
coerce_diagram_hom(C::Cat, f) = munit(DiagramHom{op}, C, f)

""" Parse expression defining a morphism of diagrams.
"""
function parse_diagram_hom(C::Cat, expr, d::Diagram{op}, c′::Some)
  DiagramHom{op}(SVector(parse_diagram_hom_rhs(C, shape(d), expr)),
                 d, munit(Diagram{op}, C, something(c′)))
end
function parse_diagram_hom(C::Cat, expr, ::Some, ::Some)
  Some(parse_hom(C, expr))
end

function parse_diagram_hom_rhs(C::Cat, J::FinCat, expr)
  g = graph(J)
  @match expr begin
    Expr(:call, :(⋅), args...) ||
    Expr(:call, :(⨟), args...) => begin
      x, f = leftmost_arg(expr, (:(⋅),:(⨟)))
      Pair(vertex_named(g, x), parse_hom(C, f))
    end
    x::Symbol => vertex_named(g, x)
  end
end

""" Left-most argument plus remainder of left-associated binary operations.
"""
function leftmost_arg(expr, ops)
  @match expr begin
    Expr(:call, op2, Expr(:call, op1, x, y), z) &&
        if op1 ∈ ops && op2 ∈ ops end => begin
      x, rest = leftmost_arg(Expr(:call, op1, x, y), ops)
      (x, Expr(:call, op2, rest, z))
    end
    Expr(:call, op, x, y) && if op ∈ ops end => (x, y)
    _ => (expr, nothing)
  end
end

end
