module CSetDataStructures
export @acset_type, @abstract_acset_type, @declare_schema, AbstractACSet

using MLStyle
using StaticArrays: StaticArray

using ..Acsets
using ..IndexUtils
using ...Theories, ...Present, ...Syntax
using ...Theories: SchemaDesc, SchemaDescType, SchemaDescTypeType
using ...Meta: strip_lines


# StructAcset Struct Generation
###############################

abstract type StructAcset{Ts<:Tuple, Schema<:SchemaDescType,Idxed} <: Acset end

q(s::Symbol) = Expr(:quote,s)
q(s::GATExpr) = q(nameof(s))

""" Creates a quoted named tuple used for `StructAcset`s
"""
function pi_type(dom::Vector, F::Function)
  :(NamedTuple{($(q.(dom)...),),Tuple{$(F.(dom)...)}})
end

""" Creates a quoted element of a named tuple used for `StructAcset`s
"""
function pi_type_elt(dom::Vector, f::Function)
  if length(dom) > 0
    Expr(:tuple, Expr(:parameters, [Expr(:kw, nameof(d), f(d)) for d in dom]...))
  else # workaround for Julia 1.0
    :(NamedTuple())
  end
end

""" Create the struct declaration for a `StructAcset` from a Presentation
"""
function struct_acset(name::Symbol, parent, p::Presentation{Schema}, idxed=[])
  obs = p.generators[:Ob]
  homs = p.generators[:Hom]
  attr_types = p.generators[:AttrType]
  Ts = nameof.(attr_types)
  attrs = p.generators[:Attr]
  idxed = (;[x => x ∈ idxed for x in [nameof.(homs);nameof.(attrs)]]...)
  indexed_homs = filter(f -> idxed[nameof(f)], homs)
  indexed_attrs = filter(a -> idxed[nameof(a)], attrs)
  param_type, new_call = if length(attr_types) > 0
    (:($name{$(nameof.(attr_types)...)}), :(new{$(nameof.(attr_types)...)}))
  else
    name, :new
  end
  schema_type = SchemaDescTypeType(p)
  quote
    struct $param_type <: $parent{Tuple{$(Ts...)}, $schema_type, $idxed}
      obs::$(pi_type(obs, _ -> :(Ref{Int})))
      homs::$(pi_type(homs, _ -> :(Vector{Int})))
      attrs::$(pi_type(attrs, a -> :(Vector{$(nameof(codom(a)))})))
      hom_indices::$(pi_type(indexed_homs, _ -> :(Vector{Vector{Int}})))
      attr_indices::$(pi_type(indexed_attrs, a -> :(Dict{$(nameof(codom(a))),Vector{Int}})))
      function $param_type() where {$(nameof.(attr_types)...)}
        $new_call(
          $(pi_type_elt(obs, _ -> :(Ref(0)))),
          $(pi_type_elt(homs, _ -> :(Int[]))),
          $(pi_type_elt(attrs, a -> :($(nameof(codom(a)))[]))),
          $(pi_type_elt(indexed_homs, _ -> :(Vector{Int}[]))),
          $(pi_type_elt(indexed_attrs, a -> :(Dict{$(nameof(codom(a))),Vector{Int}}())))
        )
      end
    end
  end
end

unquote(x::QuoteNode) = x.value

macro acset_type(head)
  head, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(CSetDataStructures, :StructAcset))
  end
  name, schema, idxed = @match head begin
    Expr(:call, name, schema, Expr(:kw,:index,idxed)) => (name, schema, unquote.(idxed.args))
    Expr(:call, name, schema) => (name, schema, Symbol[])
    _ => error("Unsupported head for @acset_type")
  end
  abstract_name = Symbol("Abstract" * string(name))
  quote
    const tmp = $(esc(:eval))($(GlobalRef(CSetDataStructures, :struct_acset))(
      $(Expr(:quote, name)), $(Expr(:quote, parent)), $(esc(schema)), $idxed))
  end
end

macro abstract_acset_type(head)
  type, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(CSetDataStructures, :StructAcset))
  end
  esc(quote
    abstract type $type{Ts,schema,idxed} <: $parent{Ts,schema,idxed} end
  end)
end


# StructAcset Operations
########################

""" This should really be in base, or at least somewhere other than this module...
"""
Base.Dict(nt::NamedTuple) = Dict(k => nt[k] for k in keys(nt))

# Accessors
###########

function Base.:(==)(x1::T, x2::T) where T <: StructAcset
  # The indices hold redundant information, so need not be compared.
  unref(x) = x[]
  unref.(values(x1.obs)) == unref.(values(x2.obs)) && x1.homs == x2.homs && x1.attrs == x2.attrs
end

Acsets.nparts(acs::StructAcset, ob::Symbol) = acs.obs[ob][]
Acsets.has_part(acs::StructAcset, ob::Symbol) = _has_part(acs, Val{ob})

@generated function _has_part(acs::StructAcset{schema}, ::Type{Val{ob}}) where
  {obs, schema <: SchemaDescType{obs}, ob}
  ob ∈ obs
end

Acsets.has_subpart(acs::StructAcset, f::Symbol) = _has_subpart(acs, Val{f})

@generated function _has_subpart(acs::StructAcset{schema}, ::Type{Val{f}}) where
  {f, obs, homs, attrtypes, attrs, schema <: SchemaDescType{obs,homs,attrtypes,attrs}}
  f ∈ homs || f ∈ attrs
end

Acsets.subpart(acs::StructAcset, f::Symbol) = _subpart(acs,Val{f})

@generated function _subpart(acs::StructAcset{Ts,schema}, ::Type{Val{f}}) where {Ts,schema, f}
  s = SchemaDesc(schema)
  if f ∈ s.homs
    :(acs.homs.$f)
  elseif f ∈ s.attrs
    :(acs.attrs.$f)
  else
    throw(ArgumentError("$(repr(f)) not in $(s.homs) or $(s.attrs)"))
  end
end

Base.getindex(acs::StructAcset, args...) = Acsets.subpart(acs, args...)

@inline Acsets.incident(acs::StructAcset, part, f::Symbol; copy::Bool=false) =
  _incident(acs, part, Val{f}; copy=copy)

broadcast_findall(xs, array::AbstractArray) =
  broadcast(x -> findall(y -> x == y, array), xs)

"""
We keep the main body of the code generating out of the @generated function
so that the code-generating function only needs to be compiled once.
"""
function incident_body(s::SchemaDesc, idxed::Dict{Symbol,Bool}, f::Symbol)
  if f ∈ s.homs
    if idxed[f]
      quote
        indices = $(GlobalRef(Acsets,:view_or_slice))(acs.hom_indices.$f, part)
        copy ? Base.copy.(indices) : indices
      end
    else
      :(broadcast_findall(part, acs.homs.$f))
    end
  elseif f ∈ s.attrs
    if idxed[f]
      quote
        indices = get_attr_index.(Ref(acs.attr_indices.$f), part)
        copy ? Base.copy.(indices) : indices
      end
    else
      :(broadcast_findall(part, acs.attrs.$f))
    end
  else
    throw(ArgumentError("$(repr(f)) not in $(s.homs)"))
  end
end
    
@generated function _incident(acs::StructAcset{Ts,schema,idxed},
                              part, ::Type{Val{f}}; copy::Bool=false) where {Ts,schema,idxed,f}
  incident_body(SchemaDesc(schema),Dict(idxed),f)
end

# Mutators
##########

Acsets.add_parts!(acs::StructAcset, ob::Symbol, n::Int) = _add_parts!(acs, Val{ob}, n)

function add_parts_body(s::SchemaDesc,idxed::Dict{Symbol,Bool},ob::Symbol)
  code = quote
    m = acs.obs.$ob[]
    nparts = m + n
    newparts = (m+1):m+n
    acs.obs.$ob[] = nparts
  end
  for f in s.homs
    if s.doms[f] == ob
      push!(code.args, quote
              resize!(acs.homs.$f, nparts)
              acs.homs.$f[newparts] .= 0
            end)
    end
    if s.codoms[f] == ob && idxed[f]
      push!(code.args, quote
            resize!(acs.hom_indices.$f, nparts)
            for i in newparts
              acs.hom_indices.$f[i] = Int[]
            end
            end)
    end
    code
  end
  for a in s.attrs
    if s.doms[a] == ob
      push!(code.args,:(resize!(acs.attrs.$a, nparts)))
    end
  end
  push!(code.args, :(newparts))
  code
end

""" This generates the _add_parts! methods for a specific object of a `StructAcset`.
"""
@generated function _add_parts!(acs::StructAcset{Ts,schema,idxed},
                                ::Type{Val{ob}}, n::Int) where {Ts, ob, schema, idxed}
  add_parts_body(SchemaDesc(schema),Dict(idxed),ob)
end

Acsets.set_subpart!(acs::StructAcset, part::Int, f::Symbol, subpart) =
  _set_subpart!(acs, part, Val{f}, subpart)


function set_subpart_body(s::SchemaDesc, idxed::Dict{Symbol,Bool}, f::Symbol)
  if f ∈ s.homs
    if idxed[f]
      quote
        @assert 0 <= subpart <= acs.obs.$(s.codoms[f])[]
        old = acs.homs.$f[part]
        acs.homs.$f[part] = subpart
        if old > 0
          @assert deletesorted!(acs.hom_indices.$f[old], part)
        end
        if subpart > 0
          insertsorted!(acs.hom_indices.$f[subpart], part)
        end
      end
    else
      quote
        @assert 0 <= subpart <= acs.obs.$(s.codoms[f])[]
        acs.homs.$f[part] = subpart
      end
    end
  elseif f ∈ s.attrs
    if idxed[f]
      quote
        if isassigned(acs.attrs.$f, part)
          old = acs.attrs.$f[part]
          unset_attr_index!(acs.attr_indices.$f, old, part)
        end
        acs.attrs.$f[part] = subpart
        set_attr_index!(acs.attr_indices.$f, subpart, part)
      end
    else
      :(acs.attrs.$f[part] = subpart)
    end
  else
    throw(ArgumentError("$(f) not in $(s.homs) or $(s.attrs)"))
  end
end

""" This generates the `_set_subparts!` method for a specific arrow (hom/attr) of a StructAcset
"""
@generated function _set_subpart!(acs::StructAcset{Ts,schema,idxed},
                                  part, ::Type{Val{f}}, subpart) where {Ts,schema,idxed,f}
  set_subpart_body(SchemaDesc(schema),Dict(idxed),f)
end

Base.setindex!(acs::StructAcset, val, part, name) = set_subpart!(acs, part, name, val)

Acsets.rem_part!(acs::StructAcset, type::Symbol, part::Int) = _rem_part!(acs, Val{type}, part)

function getassigned(acs::StructAcset, arrows, i)
  assigned_subparts = filter(f -> isassigned(subpart(acs,f),i), arrows)
  Dict(f => subpart(acs,i,f) for f in assigned_subparts)
end

function rem_part_body(s::SchemaDesc, idxed::Dict{Symbol,Bool}, ob::Symbol)
  in_homs = filter(hom -> s.codoms[hom] == ob, s.homs)
  out_homs = filter(f -> s.doms[f] == ob, s.homs)
  out_attrs = filter(f -> s.doms[f] == ob, s.attrs)
  indexed_out_homs = filter(hom -> s.doms[hom] == ob && idxed[hom], s.homs)
  indexed_attrs = filter(attr -> s.doms[attr] == ob && idxed[attr], s.attrs)
  quote
    last_part = acs.obs.$ob[]
    @assert 1 <= part <= last_part
    # Unassign superparts of the part to be removed and also reassign superparts
    # of the last part to this part.
    for hom in $(Tuple(in_homs))
      set_subpart!(acs, incident(acs, part, hom, copy=true), hom, 0)
      set_subpart!(acs, incident(acs, last_part, hom, copy=true), hom, part)
    end
    last_row = getassigned(acs, $([out_homs;out_attrs]), last_part)

    # Clear any morphism and data attribute indices for last part.
    for hom in $(Tuple(indexed_out_homs))
      set_subpart!(acs, last_part, hom, 0)
    end
    for attr in $(Tuple(indexed_attrs))
      if haskey(last_row, attr)
        unset_attr_index!(acs.attr_indices[attr], last_row[attr], last_part)
      end
    end

    # Finally, delete the last part and update subparts of the removed part.
    for f in $(Tuple(out_homs))
      resize!(acs.homs[f], last_part - 1)
    end
    for a in $(Tuple(out_attrs))
      resize!(acs.attrs[a], last_part - 1)
    end
    acs.obs.$ob[] -= 1
    if part < last_part
      set_subparts!(acs, part, (;last_row...))
    end
  end
end

@generated function _rem_part!(acs::StructAcset{Ts,schema,idxed}, ::Type{Val{ob}},
                               part::Int) where {Ts,ob,schema,idxed}
  rem_part_body(SchemaDesc(schema),Dict(idxed),ob)
end

function Base.copy(acs::StructAcset)
  new_acs = typeof(acs)()
  Acsets.copy_parts!(new_acs, acs)
  new_acs
end

""" Copy parts from a C-set to a C′-set.

The selected parts must belong to both schemas. All subparts common to the
selected parts, including data attributes, are preserved. Thus, if the selected
parts form a sub-C-set, then the whole sub-C-set is preserved. On the other
hand, if the selected parts do *not* form a sub-C-set, then some copied parts
will have undefined subparts.
"""
@generated function Acsets.copy_parts!(to::StructAcset{Ts,schema},
                                from::StructAcset{Ts′,schema′}; kw...) where {Ts, Ts′, schema, schema′}
  s, s′ = SchemaDesc(schema), SchemaDesc(schema′)
  obs = intersect(s.obs, s′.obs)
  :(copy_parts!(to, from, isempty(kw) ? $(Tuple(obs)) : (; kw...)))
end

Acsets.copy_parts!(to::StructAcset, from::StructAcset, obs::Tuple) =
  copy_parts!(to, from, NamedTuple{obs}((:) for ob in obs))
Acsets.copy_parts!(to::StructAcset, from::StructAcset, parts::NamedTuple) =
  _copy_parts!(to, from, replace_colons(from, parts))

@generated function _copy_parts!(to::StructAcset{Ts,schema}, from::StructAcset{Ts′, schema′},
                                 parts::NamedTuple{obs}) where {Ts, Ts′, schema, schema′, obs}
  s, s′ = SchemaDesc(schema), SchemaDesc(schema′)
  @assert obs ⊆ intersect(s.obs, s′.obs)
  homs = intersect(s.homs, s′.homs)
  homs = filter(homs) do hom
    c, c′, d, d′ = s.doms[hom], s′.doms[hom], s.codoms[hom], s′.codoms[hom]
    c == c′ && d == d′ && c ∈ obs && d ∈ obs
  end
  hom_triples = [ (hom, s.doms[hom], s.codoms[hom]) for hom in homs ]
  in_obs = unique!(map(last, hom_triples))
  quote
    newparts = _copy_parts_only!(to, from, parts)
    partmaps = NamedTuple{$(Tuple(in_obs))}(tuple($(map(in_obs) do type
      :(Dict{Int,Int}(zip(parts.$type, newparts.$type)))
    end...)))
    for (name, dom, codom) in $(Tuple(hom_triples))
      for (p, newp) in zip(parts[dom], newparts[dom])
        q = subpart(from, p, name)
        newq = get(partmaps[codom], q, nothing)
        if !isnothing(newq)
          set_subpart!(to, newp, name, newq)
        end
      end
    end
    newparts
  end
end

""" Copy parts from a C-set to a C′-set, ignoring all non-data subparts.

The selected parts must belong to both schemas. Attributes common to both
schemas are also copied, but no other subparts are copied.

See also: [`copy_parts!`](@ref).
"""
@generated function copy_parts_only!(to::StructAcset{Ts, schema},
                                     from::StructAcset{Ts′, schema′}; kw...) where {Ts, Ts′, schema, schema′}
  s, s′ = SchemaDesc(schema), SchemaDesc(schema′)
  obs = intersect(s.obs, s′.obs)
  :(copy_parts_only!(to, from, isempty(kw) ? $(Tuple(obs)) : (; kw...)))
end

copy_parts_only!(to::StructAcset, from::StructAcset, obs::Tuple) =
  copy_parts_only!(to, from, NamedTuple{obs}((:) for ob in obs))
copy_parts_only!(to::StructAcset, from::StructAcset, parts::NamedTuple) =
  _copy_parts_only!(to, from, replace_colons(from, parts))

@generated function _copy_parts_only!(to::StructAcset{Ts, schema}, from::StructAcset{Ts′, schema′},
    parts::NamedTuple{obs}) where {Ts, Ts′, schema, schema′, obs}
  s, s′ = SchemaDesc(schema), SchemaDesc(schema′)
  @assert obs ⊆ intersect(s.obs, s′.obs)
  attrs = intersect(s.attrs, s′.attrs)
  attrs = filter(attrs) do attr
    ob, ob′ = s.doms[attr], s′.doms[attr]
    ob == ob′ && ob ∈ obs
  end
  Expr(:block,
    :(newparts = (; $(map(obs) do ob
        Expr(:kw, ob, :(add_parts!(to, $(QuoteNode(ob)), length(parts.$ob))))
        end...))),
    map(attrs) do attr
      ob = s.doms[attr]
      :(set_subpart!(to, newparts.$ob, $(QuoteNode(attr)),
                     subpart(from, parts.$ob, $(QuoteNode(attr)))))
    end...,
    :newparts)
end

function replace_colons(acs::StructAcset, parts::NamedTuple{types}) where {types}
  NamedTuple{types}(map(types, parts) do type, part
    part == (:) ? (1:nparts(acs, type)) : part
  end)
end

# Printing
##########

function Base.show(io::IO, acs::StructAcset{Ts,schema,idxed}) where {schema,idxed,Ts}
  s = SchemaDesc(schema)
  print(io, "ACSet")
  println(io, "(")
  join(io, vcat(
    [ "  $ob = 1:$(nparts(acs,ob))" for ob in s.obs ],
    [ "  $attr_type = $(Ts.parameters[i])" for (i, attr_type) in enumerate(s.attrtypes) ],
    [ "  $f : $(s.doms[f]) → $(s.codoms[f]) = $(subpart(acs,f))"
      for f in s.homs ],
    [ "  $a : $(s.doms[a]) → $(s.codoms[a]) = $(subpart(acs,a))"
      for a in s.attrs ],
  ), ",\n")
  print(io, ")")
end

# TODO: implement Tables interface
# function Base.show(io::IO, ::MIME"text/plain", acs::StructAcset{schema}) where {schema}
#   s = SchemaDesc(schema)
#   print(io, "ACSet")
#   print(io, " with elements ")
#   join(io, ["$ob = 1:$(nparts(acs,ob))" for ob in ], ", ")
#   println(io)
#   pretty_tables(io, acs)
# end

# function Base.show(io::IO, ::MIME"text/html", acs::T) where {T<:AbstractACSet}
#   println(io, "<div class=\"c-set\">")
#   print(io, "<span class=\"c-set-summary\">")
#   print(io, T <: AbstractCSet ? "CSet" : "ACSet")
#   print(io, " with elements ")
#   join(io, ["$ob = 1:$(nparts(acs,ob))" for ob in keys(tables(acs))], ", ")
#   println(io, "</span>")
#   pretty_tables(io, acs, backend=:html, standalone=false)
#   println(io, "</div>")
# end

end
