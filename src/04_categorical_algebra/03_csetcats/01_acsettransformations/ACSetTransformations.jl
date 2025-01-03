
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
      is_cartesian, in_bounds, _ACSetTransformation

using StructEquality

using ACSets, CompTime
using ACSets.DenseACSets: attrtype_type

using ....BasicSets, ...SetCats
import ....Theories: dom, codom
import ....BasicSets: is_monic, is_epic, preimage


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
  # show_domains(io, α) # TODO
  print(io, ")")
end

type_components(α::StructACSetTransformation{S}) where S =
  NamedTuple(c => α.components[c] for c in attrtypes(S))

is_monic(α::ACSetTransformation) = all(is_monic, components(α))

is_epic(α::ACSetTransformation) = all(is_epic, components(α))


# Other constructors
####################

# WARNING that this means :cat is a reserved name for schema entities.
"""Move components as first argument"""
ACSetTransformation(X::ACSet, Y::ACSet; cat=nothing, components...) =
  ACSetTransformation((; components...), X, Y; cat)
      
# ACSetTransformation(components, X::StructACSet{S}, Y::StructACSet{S}) where {S} = 
#   _ACSetTransformation(Val{S},components,X,Y,Val{true})

# ACSetTransformation(components, X::DynamicACSet, Y::DynamicACSet) = 
#   runtime(_ACSetTransformation, X.schema, components, X,Y,false)

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
  return StructACSetTransformation{S}(NamedTuple(components), X, Y)
end

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

# Cartesian morphisms of acsets
###############################
function is_cartesian_at(f::ACSetTransformation,h::Symbol)
  X,Y = FinDomFunctor(dom(f)),FinDomFunctor(codom(f))
  S = acset_schema(dom(f))
  mor,x,y = h,dom(S,h),codom(S,h)
  s = Span(hom_map(X,mor),f[x])
  c = Cospan(f[y],hom_map(Y,mor))
  L = limit(c)
  f = universal(L,s)
  is_iso(f)
end
"""
    is_cartesian(f,hs)

Checks if an acset transformation `f` is cartesian at the homs in the list `hs`.
Expects the homs to be given as a list of `Symbol`s.
"""
is_cartesian(f,hs=homs(acset_schema(dom(f)),just_names=true)) = all(h->is_cartesian_at(f,h),hs)

end # module
