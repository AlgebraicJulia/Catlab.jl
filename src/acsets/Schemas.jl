module Schemas

export Schema, TypeLevelSchema, BasicSchema, TypeLevelBasicSchema, typelevel,
  objects, attrtypes, attrtype_instantiation, homs, attrs, arrows, dom, codom,
  ob, hom, attrtype, attr, dom_nums, codom_nums, adom_nums, acodom_nums, types

using StructEquality

# Schemas
#########

abstract type Schema{Name} end
abstract type TypeLevelSchema{Name} end

"""
Parameters:
- s::Schema{Name}

Returns an iterable of the names of the objects for this schema.
"""
function objects end

"""
Parameters:
- s::Schema{Name}

Returns an iterable of the names of the attrtypes for this schema.
"""
function attrtypes end

"""
Returns objects and attrtypes.
"""
function types end 


"""
Parameters:
- s::Schema{Name}

Named Parameters:
- just_names::Bool=false
- from::Any = nothing
- to::Any = nothing

Defaults to returning an iterable of tuples `(f,x,y)` where `f` is the name of a
homomorphism and `x` and `y` are its domain and codomain respectively.

If `just_names` is true, then it just returns the `f`s.

If `from` is not nothing then it should be either an object or an iterable of objects;
this then filters to only morphisms that have domain in `from`. Mutatis mutandis for
`to`.
"""
function homs end

"""
Parameters:
- s::Schema{Name}

Named Parameters:
- just_names::Bool=false
- from::Any = nothing
- to::Any = nothing

Same deal as [`homs`](@ref), but for attributes.
"""
function attrs end

"""
Parameters:
- s::Schema{Name}

Named Parameters:
- just_names::Bool=false
- from::Any = nothing
- to::Any = nothing

Same deal as [`homs`](@ref), but for homs and attributes.
"""
function arrows end

"""
Parameters:
- s::Schema{Name}
- f::Name

Named Parameters:
- to::Any = nothing

If `to` is nothing, then this returns the domain of the unique morphism with
name `f`, and errors otherwise. If `to` is not nothing, then it should be either
an object/attrtype or an iterable of objects/attrtypes, and this should return
the domain of the unique morphism with codomain in `to`.
"""
function dom end

"""
Parameters:
- s::Schema{Name}
- f::Name

Named Parameters:
- from::Any = nothing

Same deal as [`dom`](@ref), but for codomains.
"""
function codom end

# Basic Schemas
###############

abstract type TypeLevelBasicSchema{Name, obs, homs, attrtypes, attrs} <: TypeLevelSchema{Name} end

const TypeLevelBasicCSetSchema{Name, obs, homs} = TypeLevelBasicSchema{Name, obs, homs, Tuple{}, Tuple{}}

@struct_hash_equal struct BasicSchema{Name} <: Schema{Name}
  obs::Vector{Name}
  homs::Vector{Tuple{Name,Name,Name}}
  attrtypes::Vector{Name}
  attrs::Vector{Tuple{Name,Name,Name}}
  function BasicSchema{Name}(obs, homs, attrtypes, attrs) where {Name}
    new{Name}(obs, homs, attrtypes, attrs)
  end
  function BasicSchema(obs::Vector{Name}, homs, attrtypes, attrs) where {Name}
    new{Name}(obs, homs, attrtypes, attrs)
  end
  function BasicSchema(obs::Vector{Name}, homs) where {Name}
    new{Name}(obs, homs, Name[], Tuple{Name,Name,Name}[])
  end
end

function Schema(::Type{TypeLevelBasicSchema{Name, obs, homs, attrtypes, attrs}}) where {Name, obs, homs, attrtypes, attrs}
  BasicSchema{Name}(
    [obs.parameters...],
    [homs.parameters...],
    [attrtypes.parameters...],
    [attrs.parameters...]
  )
end

Schema(s::BasicSchema) = s

objects(s::BasicSchema) = s.obs

objects(S::Type{<:TypeLevelBasicSchema}) = Tuple(S.parameters[2].parameters)

attrtypes(s::BasicSchema) = s.attrtypes

attrtypes(S::Type{<:TypeLevelBasicSchema}) = Tuple(S.parameters[4].parameters)

types(S::Union{Schema,Type{<:TypeLevelSchema}}) = [objects(S)..., attrtypes(S)...]

attrtype_instantiation(S::Type{<:TypeLevelBasicSchema}, Ts, a::Symbol) =
  Ts.parameters[findfirst(attrtypes(S) .== a)]

attrtype_instantiation(::BasicSchema, D::AbstractDict, a::Symbol) = D[a]

contained_in(T, x, y) =
  if typeof(x) == T
    x == y
  elseif x == nothing
    true
  else
    y ∈ x
  end

function homs(s::BasicSchema{Name}; just_names=false, to=nothing, from=nothing) where {Name}
  matching = if to == nothing && from == nothing && !just_names
    s.homs
  else
    filter(((f,d,c),) -> contained_in(Name, from, d) && contained_in(Name, to, c), s.homs)
  end
  if just_names
    first.(matching)
  else
    matching
  end
end

function homs(S::Type{<:TypeLevelBasicSchema}; just_names=false, to=nothing, from=nothing)
  homs(Schema(S); just_names, to, from)
end

function attrs(s::BasicSchema{Name}; just_names=false, to=nothing, from=nothing) where {Name}
  matching = if to == nothing && from == nothing && !just_names
    s.attrs
  else
    filter(((f,d,c),) -> contained_in(Name, from, d) && contained_in(Name, to, c), s.attrs) end
  if just_names
    first.(matching)
  else
    matching
  end
end

function attrs(S::Type{<:TypeLevelBasicSchema}; just_names=false, to=nothing, from=nothing)
  attrs(Schema(S); just_names, to, from)
end

function arrows(s::BasicSchema{Name}; just_names=false, to=nothing, from=nothing) where {Name}
  matching = if to == nothing && from == nothing
    [s.homs; s.attrs]
  else
    filter(((f,d,c),) -> contained_in(Name, from, d) && contained_in(Name, to, c), [s.homs; s.attrs])
  end
  if just_names
    first.(matching)
  else
    matching
  end
end

function arrows(S::Type{<:TypeLevelBasicSchema}; just_names=false, to=nothing, from=nothing)
  arrows(Schema(S); just_names, to, from)
end

dom(s::BasicSchema{Name}, f::Name; to=nothing) where {Name} =
  only(d for (f′,d,c) in [s.homs; s.attrs] if contained_in(Name, to, c) && f′== f)

dom(S::Type{<:TypeLevelBasicSchema}, f::Name; to=nothing) where {Name} =
  dom(Schema(S), f; to)

codom(s::BasicSchema{Name}, f::Name; to=nothing) where {Name} =
  only(c for (f′,d,c) in [s.homs; s.attrs] if contained_in(Name, to, d) && f′== f)

codom(S::Type{<:TypeLevelBasicSchema}, f::Name; to=nothing) where {Name} =
  codom(Schema(S), f; to)

function typelevel(s::BasicSchema{Name}) where {Name}
  TypeLevelBasicSchema{
    Name,
    Tuple{s.obs...},
    Tuple{s.homs...},
    Tuple{s.attrtypes...},
    Tuple{s.attrs...}
  }
end

# Compatibility wrappers

ob(s) = objects(s)
hom(s) = homs(s; just_names=true)
attrtype(s) = attrtypes(s)
attr(s) = attrs(s; just_names=true)

dom_nums(s) = Tuple(findfirst(objects(s) .== d) for (_,d,_) in homs(s))
codom_nums(s) = Tuple(findfirst(objects(s) .== c) for (_,_,c) in homs(s))
adom_nums(s) = Tuple(findfirst(objects(s) .== d) for (_,d,_) in attrs(s))
acodom_nums(s) = Tuple(findfirst(attrtypes(s) .== c) for (_,_,c) in attrs(s))

end
