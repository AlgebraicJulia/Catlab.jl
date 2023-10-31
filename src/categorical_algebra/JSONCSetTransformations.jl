""" JSON serialization of acset transformations.
"""
module JSONCSetTransformations
export generate_json_fin_function, parse_json_fin_function,
  read_json_fin_function, write_json_fin_function#=,
  generate_json_acset_transformation, parse_json_acset_transformation,
  read_json_acset_transformation, write_json_acset_transformation=#

import JSON
using DataStructures: OrderedDict
#import Pkg
#import Tables

using ..FinSets, ..CSets
# TODO: Some of these `using`s might not be necessary.
using ACSets.ACSetInterface, ACSets.Schemas, ACSets.DenseACSets
using ACSets.DenseACSets: attr_type
using ACSets.ColumnImplementations: AttrVar

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
      Iterators.map((keys ∘ components)(X), (values ∘ components)(X)) do (k,v)
        k => k ∈ (attrtypes ∘ acset_schema ∘ dom)(X) ?
          "foo" :
          generate_json_fin_function(k)
      end))
end


#attr_to_json(var::AttrVar) = (_var = var.val,)
#attr_to_json(val) = val
#
#""" Parse JSON-able object or JSON string representing an ACSet.
#
#Inverse to [`generate_json_acset`](@ref).
#"""
#parse_json_acset_transformation(cons, input::AbstractDict) =
#  parse_json_acset!(cons(), input)
#parse_json_acset_transformation(cons, input::AbstractString) =
#  parse_json_acset_transformation(cons, JSON.parse(input))
#parse_json_acset_transformation(acs::ACSet, input::AbstractDict) =
#  parse_json_acset_transformation(constructor(acs), input)
#
## TODO
#function parse_json_acset_transformation!(out::ACSetTransformation, input::AbstractDict)
#  schema = acset_schema(out)
#  parts = Iterators.map(input) do (type, rows)
#    Symbol(type) => add_parts!(out, Symbol(type), length(rows))
#  end |> Dict
#  for rows ∈ values(input)
#    for (rownum, row) ∈ enumerate(rows)
#      for (k, v) ∈ pairs(row)
#        k = Symbol(k)
#        if k == :_id
#          # For now, IDs are assumed to coincide with row number.
#          @assert rownum == v
#          continue
#        end
#        if k ∈ attrs(schema; just_names=true)
#          vtype = attr_type(out, k)
#          v = v isa AbstractDict && haskey(v, "_var") ?
#            AttrVar(v["_var"]) : vtype(v)
#        end
#        set_subpart!(out, parts[dom(schema, k)][rownum], k, v)
#      end
#    end
#  end
#  out
#end
#
#""" Deserialize an ACSetTransformation object from a JSON file.
#
#Inverse to [`write_json_acset_transformation`](@ref).
#"""
#function read_json_acset_transformation(ty, fname::AbstractString)
#  parse_json_acset_transformation(ty, JSON.parsefile(fname))
#end
#
#""" Serialize an ACSetTransformation object to a JSON file.
#
#Inverse to [`read_json_acset_transformation`](@ref).
#"""
#function write_json_acset_transformation(x::ACSetTransformation, fname::AbstractString)
#  open(fname, "w") do f
#    write(f, JSON.json(generate_json_acset_transformation(x)))
#  end
#end

end # module

