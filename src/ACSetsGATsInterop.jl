""" Compatibility module that integrates ACSets with GATs.
"""
module ACSetsGATsInterop
export ThSchema, FreeSchema, Presentation, @present, getvalue

using DataStructures: OrderedDict

using ACSets
import ACSets: Schema

using GATlab
import GATlab: Presentation
using ..Theories

using MLStyle

# Schema <-> presentation
#########################

seq(f::GATExpr{:compose}) = tuple(nameof.(f.args)...)
seq(::GATExpr{:id}) = ()
seq(f::GATExpr{:generator}) = (first(f),)

function Schema(p::Presentation)
  obs, attrtypes = map(xs -> Symbol[nameof.(xs)...],
                       [p.generators[:Ob],p.generators[:AttrType]])
  homs, attrs = map(fs -> Tuple{Symbol,Symbol,Symbol}[(nameof(f), nameof(dom(f)), nameof(codom(f))) for f in fs],
                    [p.generators[:Hom], p.generators[:Attr]])
  eqs = map(equations(p)) do (l, r)
    (nothing, nameof(dom(l)), nameof(codom(l)), (seq(l), seq(r)))
  end
  BasicSchema(obs,homs,attrtypes,attrs, eqs)
end

function Schema(c::GATContext)
  obs, attrtypes = Symbol[], Symbol[]
  homs, attrs = Tuple{Symbol, Symbol, Symbol}[], Tuple{Symbol, Symbol, Symbol}[]
  for scope in allscopes(gettypecontext(c))
    for binding in scope
      type = getvalue(binding)
      @match (nameof(type.body.head), type.body.args...) begin
        (:Ob,) => push!(obs, nameof(binding))
        (:Hom, x, y) => push!(homs, nameof.((binding, x.body, y.body)))
        (:AttrType,) => push!(attrtypes, nameof(binding))
        (:Attr, x, y) => push!(attrs, nameof.((binding, x.body, y.body)))
      end
    end
  end
  return BasicSchema(obs, homs, attrtypes, attrs, [])
end

function Presentation(::Type{S}) where S <: TypeLevelBasicSchema{Symbol}
  Presentation(Schema(S))
end

function Presentation(::StructACSet{S}) where S <: TypeLevelBasicSchema{Symbol}
  Presentation(Schema(S))
end

function Presentation(d::DynamicACSet)
  Presentation(Schema(acset_schema(d)))
end


function Presentation(::Type{<:StructACSet{S}}) where S <: TypeLevelBasicSchema{Symbol}
  Presentation(Schema(S))
end

function Presentation(s::BasicSchema{Symbol})
  pres = Presentation(FreeSchema)
  obs = OrderedDict(x => Ob(FreeSchema.Ob, x) for x in Schemas.objects(s))
  attrtypes = OrderedDict(x => AttrType(FreeSchema.AttrType, x) for x in Schemas.attrtypes(s))
  homs = [Hom(f, obs[d], obs[c]) for (f,d,c) in Schemas.homs(s)]
  attrs = [Attr(f, obs[d], attrtypes[c]) for (f,d,c) in Schemas.attrs(s)]

  foreach(gens -> add_generators!(pres, gens), (values(obs), homs, values(attrtypes), attrs))
  for (_, d, cd, eqs) in equations(s)
    add_equation!(pres, mk_term.(Ref(pres), d, eqs)...)
  end
  return pres
end

mk_term(pres, dom::Symbol, ::Tuple{}) = id(Ob(FreeSchema.Ob, dom)) # id(dom)
mk_term(pres, ::Symbol, t::Tuple{Symbol}) = generator(pres, only(t)) # generator
mk_term(pres, ::Symbol, t::Tuple{Vararg{Symbol}}) = compose(generator.(Ref(pres), t)...)


function DenseACSets.struct_acset(name::Symbol, parent, p::Presentation;
                                  index::Vector=[], unique_index::Vector=[], 
                                  part_type::Type{<:PartsType}=IntParts)
  DenseACSets.struct_acset(name, parent, Schema(p); index, unique_index, part_type)
end

function DenseACSets.DynamicACSet(
  name::String,
  p::Presentation;
  type_assignment=Dict{Symbol,Type}(),
  index::Vector=[],
  unique_index::Vector=[]
  )
  DynamicACSet(name, Schema(p); type_assignment, index, unique_index)
end

function DenseACSets.DynamicACSet(name::String, p::Presentation, type_assignment, parts, subparts)
  DynamicACSet(name, Schema(p), type_assignment, parts, subparts)
end

function AnonACSetType(p::Presentation; kwargs...)
  AnonACSetType(Schema(p); kwargs...)
end

function DenseACSets.AnonACSet(p::Presentation; kwargs...)
  AnonACSet(Schema(p); kwargs...)
end

# JSON serialization
#-------------------

JSONACSets.generate_json_acset_schema(pres::Presentation) =
  generate_json_acset_schema(Schema(pres))

JSONACSets.parse_json_acset_schema(::Type{Presentation},
                                   data::AbstractDict) =
  Presentation(parse_json_acset_schema(BasicSchema, data))
JSONACSets.parse_json_acset_schema(data) =
  parse_json_acset_schema(Presentation, data)

JSONACSets.read_json_acset_schema(fname::AbstractString) =
  read_json_acset_schema(Presentation, fname)

# ACSet <-> GAT exprs
#####################

subpart_names(expr::GATExpr{:generator}) = Symbol[first(expr)]
subpart_names(expr::GATExpr{:id}) = Symbol[]
subpart_names(expr::GATExpr{:compose}) =
  mapreduce(subpart_names, vcat, args(expr))

ACSetInterface.subpart(acs, expr::GATExpr{:compose}) = subpart(acs, subpart_names(expr))

ACSetInterface.subpart(acs, part, expr::GATExpr{:compose}) =
  subpart(acs, part, subpart_names(expr))

@inline ACSetInterface.subpart(acs, expr::GATExpr{:generator}) = subpart(acs, first(expr))
@inline ACSetInterface.subpart(acs, i, expr::GATExpr{:generator}) = subpart(acs, i, first(expr))
@inline ACSetInterface.subpart(acs, expr::GATExpr{:id}) = parts(acs, first(dom(expr)))
@inline ACSetInterface.subpart(acs, i::Int, ::GATExpr{:id}) = i
@inline ACSetInterface.subpart(acs, i::AbstractVector{Int}, ::GATExpr{:id}) = i
@inline ACSetInterface.subpart(acs, ::Colon, ::GATExpr{:id}) = parts(acs, first(dom(expr)))

ACSetInterface.incident(acs, part, expr::GATExpr; kw...) =
  incident(acs, part, subpart_names(expr); kw...)

end
