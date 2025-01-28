
""" Transformation between attributed C-sets.

A *homomorphism* of attributed C-sets with schema S: C ↛ A (a profunctor) is a
natural transformation between the corresponding functors col(S) → Set, where
col(S) is the collage of S. When the components on attribute types, indexed by
objects of A, are all identity functions, the morphism is called *tight*; in
general, it is called *loose*. With this terminology, acsets on a fixed schema
are the objects of an ℳ-category (see `Catlab.Theories.MCategory`). Calling
`ACSetTransformation` will construct a tight or loose morphism as appropriate,
depending on which components are specified.

Since every tight morphism can be considered a loose one, the distinction
between tight and loose may seem a minor technicality, but it has important
consequences because limits and colimits in a category depend as much on the
morphisms as on the objects. In particular, limits and colimits of acsets differ
greatly depending on whether they are taken in the category of acsets with tight
morphisms or with loose morphisms. Tight morphisms suffice for many purposes,
including most applications of colimits. However, when computing limits of
acsets, loose morphisms are usually preferable. For more information about
limits and colimits in these categories, see [`ACSetTight`](@ref)
and [`ACSetLoose`](@ref).
"""
module ACSetTransformations 

export ACSetTransformation, StructACSetTransformation, 
       DynamicACSetTransformation, components, coerce_component,
      in_bounds, _ACSetTransformation, infer_acset_cat,
      is_epic, is_monic

using StructEquality

using ACSets, CompTime
import ACSets: TypeLevelBasicSchema
using ACSets.DenseACSets: attrtype_type

using ....BasicSets, ...Cats, ...SetCats
import ....Theories: dom, codom
import ....BasicSets: is_monic, is_epic, preimage
import ...Cats: components


""" Transformation between attributed C-sets.

Subtypes of ACSetTransformation contain some (pointwise) SetFunctions
relating two ACSets. This data can only be interpreted in the context of some
category, such as the category of C-Sets, the category of ACSets with tight
transformations, VarACSets, the category of C-Par. In each case there may be
restrictions on what type of data is permitted in the components, but that
validation should happen elsewhere.
"""
abstract type ACSetTransformation end

components(α::ACSetTransformation) = α.components

dom(α::ACSetTransformation) = α.dom 
codom(α::ACSetTransformation) = α.codom 

"""
ACSetTransformation where schema is known at compile time, which can be used for 
performance optimizations.
"""
@struct_hash_equal struct StructACSetTransformation{
    S <: TypeLevelSchema, Comp <: NamedTuple, Dom <: StructACSet{S},
    Codom <: StructACSet{S}} <: ACSetTransformation
  components::Comp
  dom::Dom
  codom::Codom  
end

"""
ACSeTransformation where schema not known at compile time.
"""
@struct_hash_equal struct DynamicACSetTransformation <: ACSetTransformation
  components::NamedTuple
  dom::ACSet
  codom::ACSet
end

# Other methods
###############

function Base.getindex(α::ACSetTransformation, c) 
  get(α.components, c) do
    c ∈ attrtypes(acset_schema(dom(α))) || error("No object or attribute type with name $c")
    SetFunction(identity, TypeSet(dom(α),c), TypeSet(codom(α),c))
  end
end

function Base.show(io::IO, α::ACSetTransformation)
  print(io, "ACSetTransformation(")
  show(io, components(α))
  print(io, ", ")
  # show_domains(io, α) # KBTODO
  print(io, ")")
end

type_components(α::StructACSetTransformation{S}) where S =
  NamedTuple(c => α.components[c] for c in attrtypes(S))

function get_set end # define in CSets 
function get_fn end # define in CSets 
function get_attrtype end # define in CSets 
function get_op_fn end # define in CSets 
function coerce_hom end # define in Csets
function coerce_op end # define in CSets

is_monic(α::ACSetTransformation; cat=nothing) =
all(functions(α; cat = isnothing(cat) ? infer_acset_cat(α) : cat)) do f 
  f isa FinFunction && return is_monic(f)
  # otherwise let's assume it's a kleisli map. We just care if monic on Left
  vals = collect(f)
  all(x -> x isa Left, vals) || return false 
  length(unique(vals)) == length(vals)
end

is_epic(α::ACSetTransformation; cat=nothing) =
  all(functions(α; cat = isnothing(cat) ? infer_acset_cat(α) : cat)) do f 
    f isa FinFunction && return is_epic(f)
    # otherwise let's assume it's a kleisli map. We just care if epic on Left
    collect(left(getvalue(codom(f)))) ⊆ [getvalue(v) for v in f if v isa Left]
  end

ACSets.acset_schema(α::ACSetTransformation) = acset_schema(dom(α))

""" Coerce the component data to be Fin(Dom)Functions """
function functions(α::ACSetTransformation; cat=nothing)
  cat = isnothing(cat) ? infer_acset_cat(α) : cat
  ent = Dict(map(ob(acset_schema(cat))) do o 
    o => get_fn(cat, α, o)
  end)
  atr = Dict(map(attrtypes(acset_schema(cat))) do o 
    o => get_op_fn(cat, α, o)
  end)
  NamedTuple(merge(ent, atr))
end



# Other constructors
####################

# WARNING that this means :cat is a reserved name for schema entities.
"""Move components as first argument"""
function ACSetTransformation(X::ACSet, Y::ACSet; cat=nothing, components...)
  ACSetTransformation((; components...), X, Y; cat)
end

function _ACSetTransformation(components, X::StructACSet{S}, Y::StructACSet{S}
                             ) where S
  return StructACSetTransformation(NamedTuple(components), X, Y)
end

function _ACSetTransformation(components, X::ACSet, Y::ACSet)
  S = acset_schema(X)
  all(collect(keys(components))) do x 
    x ∈ objects(S) ∪ attrtypes(S) || error(
      "Not all names in $x are objects or attribute types")
  end
  return DynamicACSetTransformation(NamedTuple(components), X, Y)
end


# Must be implemented after the pointwise cats are defined
infer_acset_cat(f::ACSetTransformation) = 
  infer_acset_cat(components(f), dom(f), codom(f))

# Mark as deleted
#################

"""
Check whether an ACSetTransformation is still valid, despite possible deletion 
of elements in the codomain. An ACSetTransformation that isn't in bounds will 
throw an error, rather than return `false`, if run through `is_natural`.
"""
function in_bounds(f::ACSetTransformation) 
  X, Y = dom(f), codom(f)
  S = acset_schema(X)
  all(ob(S)) do o 
    all(parts(X, o)) do i 
      f[o](i) ∈ parts(Y, o)
    end
  end || return false
  all(attrtypes(S)) do o 
    all(AttrVar.(parts(X, o))) do i 
      j = f[o](i) 
      !(j isa AttrVar) || j.val ∈ parts(Y, o)
    end
  end
end

end # module
