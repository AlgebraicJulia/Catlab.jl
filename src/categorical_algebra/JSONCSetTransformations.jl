""" JSON serialization of acset transformations.
"""
module JSONCSetTransformations
export generate_json_fin_function, parse_json_fin_function,
  read_json_fin_function, write_json_fin_function,
  generate_json_acset_transformation, parse_json_acset_transformation,
  read_json_acset_transformation, write_json_acset_transformation

import JSON
using DataStructures: OrderedDict

using ..FinSets, ..CSets

# ACSetTransformation serialization
#####################

""" Generate JSON-able object representing a FinFunction.

Inverse to [`parse_json_fin_function`](@ref).
"""
function generate_json_fin_function(F::FinFunction)
  OrderedDict{Symbol,Any}(
    :dom        => dom(    F),
    :codom      => codom(  F),
    :map => collect(F))
end

""" Serialize a FinFunction object to a JSON file.

Inverse to [`read_json_fin_function`](@ref).
"""
function write_json_fin_function(x::FinFunction, fname::AbstractString)
  open(fname, "w") do f
    write(f, JSON.json(generate_json_fin_function(x)))
  end
end

function parse_json_fin_function(input::AbstractDict)
  FinFunction(
              Int.(input["map"]), 
              input["dom"]["n"], 
              input["codom"]["n"])
end

""" Deserialize a FinFunction object from a JSON file.

Inverse to [`write_json_fin_function`](@ref).
"""
function read_json_fin_function(fname::AbstractString)
  parse_json_fin_function(JSON.parsefile(fname))
end

""" Generate JSON-able object representing an ACSetTransformation.

Inverse to [`parse_json_acset_transformation`](@ref).
"""
function generate_json_acset_transformation(X::ACSetTransformation)
  OrderedDict{Symbol,Any}(
    :dom   => (generate_json_acset ∘   dom)(X),
    :codom => (generate_json_acset ∘ codom)(X),
    :components => OrderedDict{Symbol,Any}(
      Iterators.map((keys ∘ components)(X), (values ∘ components)(X)) do k,v
        k , k ∈ (attrtypes ∘ acset_schema ∘ dom)(X) ?
          # TODO: Support VarFunctions that are not empty.
          "TODO: VarFunctions are current not supported." :
          generate_json_fin_function(v)
      end))
end

""" Serialize an ACSetTransformation object to a JSON file.

Inverse to [`read_json_acset_transformation`](@ref).
"""
function write_json_acset_transformation(x::ACSetTransformation, fname::AbstractString)
  open(fname, "w") do f
    write(f, JSON.json(generate_json_acset_transformation(x)))
  end
end

""" Parse JSON-able object or JSON string representing an ACSetTransformation.

Inverse to [`generate_json_acset_transformation`](@ref).
"""
parse_json_acset_transformation(cons, input::AbstractString) =
  parse_json_acset_transformation(cons, JSON.parse(input))
parse_json_acset_transformation(acs::ACSet, input::AbstractDict) =
  parse_json_acset_transformation(constructor(acs), input)

function parse_json_acset_transformation(cons, input::AbstractDict)
  domain   = parse_json_acset(cons(), input["dom"])
  codomain = parse_json_acset(cons(), input["codom"])
  hom_keys = filter(keys(input["components"])) do k
    Symbol(k) ∉ (attrtypes ∘ acset_schema)(domain)
  end
  # TODO: Support VarFunctions that are not empty.
  ACSetTransformation(
    NamedTuple{Tuple(Symbol.(hom_keys))}(
      Iterators.map(hom_keys) do k
        parse_json_fin_function(input["components"][k])
      end),
    domain,
    codomain)
end

""" Deserialize an ACSetTransformation object from a JSON file.

Inverse to [`write_json_acset_transformation`](@ref).
"""
function read_json_acset_transformation(ty, fname::AbstractString)
  parse_json_acset_transformation(ty, JSON.parsefile(fname))
end

end # module

