export MonoidalSchema, FreeMonoidalSchema

using AutoHashEquals

""" The GAT that parameterizes pacsets (product acsets)

A monoidal schema is comprised of a monoidal category split into two parts, one
of which is discrete.

In theory you should be able to take monoidal products of attributes/attribute
types, but I'm too lazy to write that down right now.
"""
@theory MonoidalSchema{Ob,Hom,AttrType,Attr} <: MonoidalCategory{Ob,Hom} begin
  AttrType::TYPE
  Attr(dom::Ob,codom::AttrType)::TYPE

  """ Composition is given by the action of the profunctor on C.
  """
  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ (A::Ob, B::Ob, X::AttrType)

  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ (A::Ob, B::Ob, C::Ob, X::AttrType, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)))
  compose(id(A), a) == a ⊣ (A::Ob, X::AttrType, a::Attr(A,X))
end

@syntax FreeMonoidalSchema{ObExpr,HomExpr,AttrTypeExpr,AttrExpr} MonoidalSchema begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  # should have a normal representation for precompose of a morphism + a generator attribute
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(f::Hom, x::Attr) = associate_unit(new(f,x; strict=true), id)
end

""" A monoidal schema encoded in a type, using a whole-grained Petri net like
encoding

All of the parameters are tuples of symbols. Obs, Homs, AttrTypes, and Attrs all
give the names for the generators, and InputOb, InputMorph, OutputOb,
OutputMorph give the inputs and outputs of the homs/attrs, whole-grained Petri
net style
"""
struct MSchemaDescType{Obs, Homs, AttrTypes, Attrs, InputOb, InputMorph, OutputOb, OutputMorph}
end

@auto_hash_equals struct MSchemaDesc
  obs::Vector{Symbol}
  homs::Vector{Symbol}
  attrtypes::Vector{Symbol}
  attrs::Vector{Symbol}
  doms::Dict{Symbol, Vector{Symbol}}
  codoms::Dict{Symbol, Vector{Symbol}}
end

function push_to_index!(d::Dict{K,Vector{V}}, k::K, v::V) where {K,V}
  if !(k ∈ keys(d))
    d[k] = V[]
  end
  push!(d[k], v)
end

function MSchemaDesc(
  ::Type{MSchemaDescType{Obs, Homs, AttrTypes, Attrs,
                         InputOb, InputMorph, OutputOb, OutputMorph}}) where
    {Obs, Homs, AttrTypes, Attrs, InputOb, InputMorph, OutputOb, OutputMorph}
  @assert length(InputOb) == length(InputMorph) && length(OutputOb) == length(OutputMorph)
  obs = Symbol[Obs...]
  homs = Symbol[Homs...]
  attrtypes = Symbol[AttrTypes...]
  attrs = Symbol[Attrs...]
  doms = Dict{Symbol, Vector{Symbol}}()
  codoms = Dict{Symbol, Vector{Symbol}}()
  for (x,f) in zip([InputOb...], [InputMorph...])
    push_to_index!(doms, f, x)
  end
  for (x,f) in zip([OutputOb...], [OutputMorph...])
    push_to_index!(codoms, f, x)
  end
  MSchemaDesc(obs, homs, attrtypes, attrs, doms, codoms)
end

normalize_monoidal_ob(_::ObExpr{:munit}) = Symbol[]
normalize_monoidal_ob(x::ObExpr{:generator}) = [nameof(x)]
normalize_monoidal_ob(x::ObExpr{:otimes}) = vcat(normalize_monoidal_ob.(x.args)...)


function MSchemaDesc(p::Presentation)
  obs,homs,attrtypes,attrs = map(t -> p.generators[t],[:Ob,:Hom,:AttrType,:Attr])
  ob_syms,hom_syms,attrtype_syms,attr_syms = map(xs -> nameof.(xs),
                                                 [obs,homs,attrtypes,attrs])
  hom_doms = Dict(nameof(f) => normalize_monoidal_ob(dom(f)) for f in homs)
  attr_doms = Dict(nameof(f) => normalize_monoidal_ob(dom(f)) for f in attrs)
  hom_codoms = Dict(nameof(f) => normalize_monoidal_ob(codom(f)) for f in homs)
  attr_codoms = Dict(nameof(f) => [nameof(codom(f))] for f in attrs)

  MSchemaDesc(
    ob_syms, hom_syms, attrtype_syms, attr_syms,
    Dict(hom_doms..., attr_doms...),
    Dict(hom_codoms..., attr_codoms...)
  )
end

function MSchemaDescTypeType(s::MSchemaDesc)
  input_obs = Symbol[]
  input_morphs = Symbol[]
  output_obs = Symbol[]
  output_morphs = Symbol[]
  for (f,ins) in s.doms
    append!(input_obs, ins)
    append!(input_morphs, fill(f, length(ins)))
  end
  for (f,outs) in s.codoms
    append!(output_obs, outs)
    append!(output_morphs, fill(f, length(outs)))
  end
  MSchemaDescType{Tuple(s.obs), Tuple(s.homs), Tuple(s.attrtypes), Tuple(s.attrs),
                  Tuple(input_obs), Tuple(input_morphs), Tuple(output_obs), Tuple(output_morphs)}
end

function MSchemaDescTypeType(p::Presentation)
  MSchemaDescTypeType(MSchemaDesc(p))
end
