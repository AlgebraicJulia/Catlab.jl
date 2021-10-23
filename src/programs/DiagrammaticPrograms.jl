""" DSLs for defining categories, diagrams, and related structures.

Here "diagram" means diagram in the standard category-theoretic sense, not
string diagram or wiring diagram. DSLs for constructing wiring diagrams are
provided by other submodules.
"""
module DiagrammaticPrograms
export @graph, @fincat, @finfunctor, @diagram, @migration

using Base.Iterators: repeated
using MLStyle: @match
using StaticArrays: SVector

using ...Syntax, ...Present, ...Graphs, ...CategoricalAlgebra
using ...Theories: munit
using ...Graphs.BasicGraphs: TheoryGraph

# Data types
############

@present TheoryNamedGraph <: TheoryGraph begin
  Name::AttrType
  vname::Attr(V, Name)
  ename::Attr(E, Name)
end

""" Default graph type for [`@fincat`](@ref) macro and related macros.
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

vertex_name(g::HasGraph, args...) = subpart(g, args..., :vname)
edge_name(g::HasGraph, args...) = subpart(g, args..., :ename)

vertex_named(g::HasGraph, name) = incident(g, name, :vname)
edge_named(g::HasGraph, name)= incident(g, name, :ename)

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
@fincat begin
  V, E
  (δ₀, δ₁): V → E
  σ₀: E → V

  σ₀ ∘ δ₀ == id(V)
  σ₀ ∘ δ₁ == id(V)
end
```

The objects and morphisms must be uniquely named.
"""
macro fincat(body)
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
      _ => error("@fincat macro cannot parse line: $expr")
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
      Expr(:call, :id, x::Symbol) => empty(Path, g, vertex_named(g, x))
      f::Symbol => Path(g, edge_named(g, f))
      _ => error("Invalid morphism expression $expr")
    end
  end
  parse(expr)
end

# Functors
##########

""" Define a functor between two finitely presented categories.

Such a functor is defined by sending the object and morphism generators of the
domain category to generic object and morphism expressions in the codomain
category. For example, the following functor embeds the schema for graphs into
the schema for circular port graphs by ignoring the ports:

```julia
@finfunctor TheoryGraph ThCPortGraph begin
  V => Box
  E => Wire
  src => src ⨟ box
  tgt => tgt ⨟ box
end
```
"""
macro finfunctor(dom_cat, codom_cat, body)
  :(parse_functor($(esc(dom_cat)), $(esc(codom_cat)), $(Meta.quot(body))))
end

function parse_functor(C::FinCat, D::FinCat, body::Expr; preprocess::Bool=true)
  assignments = Dict{Symbol,Union{Expr,Symbol}}()
  if preprocess
    body = Base.remove_linenums!(body)
  end
  for expr in body.args
    @match expr begin
      Expr(:call, :(=>), lhs::Symbol, rhs) => begin
        haskey(assignments, lhs) &&
          error("Left-hand side already assigned in expression $expr")
        assignments[lhs] = rhs
      end
      _ => error("Invalid assignment expression $expr")
    end
  end
  F_ob = make_map(ob_generators(C)) do x
    ob_named(D, get(assignments, ob_name(C, x)) do
      error("Object $(ob_name(C, x)) is not assigned")
    end)
  end
  F_hom = make_map(hom_generators(C)) do f
    parse_hom(D, get(assignments, hom_name(C, f)) do
      error("Morphism $(hom_name(C, f)) is not assigned")
    end)
  end
  F = FinFunctor(F_ob, F_hom, C, D)
  is_functorial(F, check_equations=false) ||
    error("Assignment is not functorial: $body")
  return F
end
function parse_functor(C::Presentation, D::Presentation, body::Expr; kw...)
  parse_functor(FinCat(C), FinCat(D), body; kw...)
end

make_map(f, xs::UnitRange{Int}) = map(f, xs)
make_map(f, xs) = Dict(x => f(x) for x in xs)

""" Parse expression for morphism in a category.
"""
function parse_hom(C::FinCat, expr)
  function parse(expr)
    @match expr begin
      Expr(:call, :compose, args...) =>
        mapreduce(parse, (fs...) -> compose(C, fs...), args)
      Expr(:call, :(⋅), f, g) ||
      Expr(:call, :(⨟), f, g) => compose(C, parse(f), parse(g))
      Expr(:call, :(∘), f, g) => compose(C, parse(g), parse(f))
      Expr(:call, :id, x::Symbol) => id(C, ob_named(C, x))
      f::Symbol => hom_named(C, f)
      _ => error("Invalid morphism expression $expr")
    end
  end
  parse(expr)
end

ob_name(C::FinCat, x) = Symbol(x)
ob_name(C::FinCat, x::GATExpr) = nameof(x)
ob_name(C::FinCatGraph, x) = vertex_name(graph(C), x)
hom_name(C::FinCat, f) = Symbol(f)
hom_name(C::FinCat, f::GATExpr) = nameof(f)
hom_name(C::FinCatGraph, f) = edge_name(graph(C), f)

ob_named(C::FinCat, name) = ob(C, name)
ob_named(C::FinCatGraph, name) = vertex_named(graph(C), name)
hom_named(C::FinCat, name) = hom(C, name)
hom_named(C::FinCatGraph, name) = edge_named(graph(C), name)

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
macro diagram(cat, body)
  :(parse_diagram($(esc(cat)), $(Meta.quot(body))))
end

function parse_diagram(C::Cat, body::Expr; preprocess::Bool=true)
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
    error("@diagram macro defined diagram  is not functorial: $expr")
  return F
end
function parse_diagram(pres::Presentation, body::Expr; kw...)
  parse_diagram(FinCat(pres), body; kw...)
end

# Data migrations
#################

struct UnitQuery{C<:FinCat,Ob}
  cat::C
  ob::Ob
end
struct UnitQueryHom{C<:FinCat,Hom}
  cat::C
  hom::Hom
end

const ConjQuery{C<:FinCat} = Diagram{op,C}
const GlueQuery{C<:FinCat} = Diagram{id,C}
const GlueConjQuery{C<:FinCat} = Diagram{id,<:TypeCat{<:Diagram{op,C}}}

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
  F_ob, F_hom = Union{UnitQuery,Diagram}[], Union{UnitQueryHom,DiagramHom}[]
  if preprocess
    body = preprocess_expr!(body)
  end
  for expr in body.args
    @match expr begin
      # x => y
      Expr(:call, :(=>), x::Symbol, y::Symbol) => begin
        add_vertex!(tgt_graph, vname=x)
        push!(F_ob, UnitQuery(src_schema, y))
      end
      # x => @limit ...
      # x => @join ...
      Expr(:call, :(=>), x::Symbol, Expr(:macrocall, form, args...)) &&
          if form ∈ (Symbol("@limit"), Symbol("@join")) end => begin
        D = parse_diagram(src_schema, last(args), preprocess=false)
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
  query_type = mapreduce(typeof, promote_query_type, F_ob,
                         init=UnitQuery{typeof(src_schema)})
  F_ob = map(x -> convert_query(query_type, x), F_ob)
  F_hom = map(f -> convert_query_hom(query_type, f), F_hom)
  J = isempty(tgt_eqs) ? FinCat(tgt_graph) : FinCat(tgt_graph, tgt_eqs)
  F = if query_type <: UnitQuery
    FinDomFunctor(map(x -> x.ob, F_ob), map(f -> f.hom, F_hom), J, src_schema)
  else
    FinDomFunctor(F_ob, F_hom, J)
  end
  is_functorial(F, check_equations=false) ||
    error("@migration macro defined diagram that is not functorial: $F")
  return F
end

""" Parse expression defining a morphism of diagrams.
"""
function parse_diagram_hom(C::Cat, expr, d::Diagram{op}, c′::UnitQuery)
  DiagramHom{op}(SVector(parse_diagram_hom_rhs(C, shape(d), expr)),
                 d, munit(Diagram{op}, C, c′.ob))
end
function parse_diagram_hom(C::Cat, expr, ::UnitQuery, ::UnitQuery)
  UnitQueryHom(C, parse_hom(C, expr))
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

# Query promotion
#----------------

promote_query_rule(::Type, ::Type) = Union{}
promote_query_rule(::Type{<:ConjQuery{C}},
                   ::Type{<:UnitQuery{C}}) where C = ConjQuery{C}

promote_query_type(T, S) = promote_query_result(
  T, S, Union{promote_query_rule(T,S), promote_query_rule(S,T)})
promote_query_result(T, S, ::Type{Union{}}) = typejoin(T, S)
promote_query_result(T, S, U) = U

convert_query(::Type{T}, x::S) where {T, S<:T} = x
convert_query(::Type{<:ConjQuery{C}}, x::UnitQuery{C}) where C =
  munit(Diagram{op}, x.cat, x.ob)

convert_query_hom(T::Type, f) = convert_query_hom(T, query_typeof(f), f)
convert_query_hom(::Type{T}, ::Type{S}, f) where {T, S<:T} = f
convert_query_hom(::Type{<:ConjQuery{C}}, ::Type{<:UnitQuery{C}}, f) where C =
  munit(DiagramHom{op}, f.cat, f.hom)

query_typeof(::DiagramHom{T,C}) where {T,C} = Diagram{T,C}
query_typeof(::UnitQueryHom{C}) where C = UnitQuery{C}

# Utilities
###########

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
