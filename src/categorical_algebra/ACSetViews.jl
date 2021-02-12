""" Data structure for views of attributed C-sets
"""
module ACSetViews
export ACSetView, backing, @compute_prop, @select_where,
  ACSetViewMorphism

using ...CSetDataStructures
using ..CSets
using ..FinSets
using ...Theories: CatDesc, AttrDesc, dom, codom_num, attr

using MLStyle: @match
using PrettyTables: pretty_table
using Tables

# Data types
############

""" One useful way of thinking of ACSetViews is that they are
dataframes backed by ACSets.

They are also useful for computing limits

P is a symbol, the object in the schema that the view focuses onto
"""
struct ACSetView{A <: ACSet, P, Attrs <: NamedTuple} <: AbstractArray{Attrs,1}
  backing :: A
  parts :: AbstractVector{Int}
  function ACSetView(backing::A, P::Symbol, parts::AbstractVector{Int}) where
      {CD <: CatDesc,AD <: AttrDesc{CD},Ts <: Tuple, A <: ACSet{CD,AD,Ts}}
    attr_names = filter(a -> dom(AD,a) == P, attr(AD))
    attr_types = map(a -> Ts.parameters[codom_num(AD,a)], attr_names)
    row_type = NamedTuple{attr_names, Tuple{attr_types...}}
    new{A,P,row_type}(backing,parts)
  end
  function ACSetView(backing::A, P::Symbol) where
      {CD <: CatDesc,AD <: AttrDesc{CD},Ts <: Tuple, A <: ACSet{CD,AD,Ts}}
    ACSetView(backing,P,1:nparts(backing,P))
  end
end

# We're going to overload getproperty, so we use these instead

backing(av::ACSetView) = getfield(av,:backing)

CSetDataStructures.parts(av::ACSetView) = getfield(av,:parts)


# Overloaded accessors
######################

Base.size(av::ACSetView) = size(parts(av))

@generated function Base.getindex(av::ACSetView{<:ACSet,P,Attrs}, i::Int) where
    {P, Attrs <: NamedTuple}
  tuple_args = map(Attrs.parameters[1]) do attr
    :($attr = av[i,$(Expr(:quote, attr))])
  end
  Expr(:tuple,tuple_args...)
end

function Base.getindex(av::ACSetView{<:ACSet,P,<:NamedTuple},i::Int,name::Union{Symbol,Vector{Symbol}}) where {P}
  subpart(backing(av), parts(av)[i], name)
end

function Base.getindex(av::ACSetView{<:ACSet,P,<:NamedTuple},i,name::Union{Symbol,Vector{Symbol}}) where {P}
  subpart(backing(av), view(parts(av),i), name)
end

function Base.getindex(av::ACSetView{<:ACSet,P,<:NamedTuple},name::Union{Symbol,Vector{Symbol}}) where {P}
  subpart(backing(av), parts(av), name)
end

function Base.getindex(av::ACSetView{<:ACSet,P,<:NamedTuple},indicator::BitArray{1}) where {P}
  ACSetView(backing(av),P,parts(av)[indicator])
end

Base.getproperty(av::ACSetView, name::Symbol) =
  subpart(backing(av), parts(av), name)

function Base.show(io::IO, ::MIME"text/plain", av::T) where {ACS <: AbstractACSet, P, T<:ACSetView{ACS,P}}
  print(io, "ACSetView of object $P")
  println(io)
  table = tables(backing(av))[P][parts(av)]
  if !(eltype(table) <: NamedTuple{(),Tuple{}} || isempty(table))
    pretty_table(io, table, nosubheader=true,
                 show_row_number=true, row_number_column_title=string(P))
  end
end

# Tables.jl interface
#####################

Tables.istable(av::ACSetView) = true

Tables.columnaccess(av::ACSetView) = true
Tables.columns(av::ACSetView) = av

function Tables.getcolumn(av::ACSetView{<:ACSet,P,Attrs}, i::Int) where {P, Attrs <: NamedTuple}
  av[:,Attrs.parameters[1][i]]
end

Tables.getcolumn(av::ACSetView, nm::Symbol) = av[:,nm]

Tables.getcolumn(av::ACSetView, i::Int, nm::Symbol) = av[i,nm]

Tables.columnnames(av::ACSetView{<:ACSet,P,Attrs}) where {P,Attrs<:NamedTuple} = Attrs.parameters[1]

# Macros for Querying/filtering
###############################

""" This macro takes an expression using attributes of the object selected by the ACSetView,
and returns an array of the result of that expression applied to the attribute of each part
in the ACSetView.

Example: @compute_prop(edges_table, 2 * src.weight)

Eventually, this should be superceded by Query.jl or AlgebraicRelations.jl functionality, so I have
purposely made the name a bit obtuse and awkward.

However, currently these have functionality not replicated by Query.jl: the ability to use compound attributes.
TODO: Add this functionality to Query.jl
"""
macro compute_prop(av, ex)
  :(@. $(replace_symbols(esc(av), ex)))
end

replace_symbols(av, ex::Symbol) = :($av[$(Expr(:quote, ex))])

function replace_symbols(av, ex::Expr)
  @match ex begin
    Expr(:call, f, args...) => Expr(:call, esc(f), map(arg -> replace_symbols(av,arg), args)...)
    Expr(:$, arg) => esc(arg)
    Expr(:., args...) => :($av[$(flatten_dot_expr(ex))])
    _ => error("unsupported syntax in @query")
  end
end

replace_symbols(av, ex) = ex

function flatten_dot_expr(ex::Expr)
  @match ex begin
    Expr(:., x, y) => [flatten_dot_expr(x)..., y.value]
    _ => error("unsupported syntax in @query")
  end
end

function flatten_dot_expr(ex::Symbol)
  [ex]
end

""" This macro takes in a similar expression to @compute_prop, except that the expression
should return a boolean, and then it returns a new ACSetView containing only the parts
that return true when the expression is applied to them.

Again, eventually this should be superceded by Query.jl or AlgebaricRelations.jl, but again
there is current functionality that is not available in either.
"""
macro select_where(av, ex)
  :($(esc(av))[@. $(replace_symbols(esc(av), ex))])
end

# Morphisms
###########

struct ACSetViewMorphism{AV <: ACSetView}
  f::FinFunction{Int,Int}
  dom::AV
  codom::AV
  function ACSetViewMorphism{AV}(f::FinFunction, dom::AV, codom::AV) where {AV <: ACSetView}
    @assert length(dom(f)) == size(dom)
    @assert length(codom(f)) == size(codom)
    new{AV}(f,dom,codom)
  end
  function ACSetViewMorphism(α::ACSetTransformation,P::Symbol)
    dom = ACSetView(α.dom,P)
    codom = ACSetView(α.codom,P)
    f = α.components[P]
    new{typeof(dom)}(f,dom,codom)
  end
end

function CSets.is_natural(α::ACSetViewMorphism)
  all(α.dom[i] == α.codom[α.f(i)] for i in eachindex(α.dom))
end

end
