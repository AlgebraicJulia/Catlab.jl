module SubCSets

export SubACSet, SubACSetComponentwise, SubACSetPointwise

using StructEquality 

using ACSets, GATlab

import .....Theories: ob, hom, top, bottom, meet, join

using .....BasicSets, ...Cats, ...SetCats
import .....BasicSets: preimage, left
import ...Cats: components, implies, subtract, negate, non, force
using ..Pointwise

using Base.Meta: quot

# Sub-C-sets
############

""" assume a VarFunction is secretly a FinFunction """
function left(f::FinDomFunction)::FinFunction
  FinFunction(map(collect(f)) do i
    i isa Left ? getvalue(i) : error(
      "Tried to coerce VarFunction $f to FinFunction, got value $i")
  end, FinSet(codom[SkelKleisli(Any)](f)))
end

""" Sub-C-set of a C-set.
"""
const SubACSet{S} = Subobject{<:StructACSet{S}}

""" 
Componentwise subobjects: note we must coerce VarFunctions (which only make 
reference to AttrVars) into FinFunctions 
"""
function components(A::SubACSet{S}) where S 
  𝒞 = infer_acset_cat(ob(A))
  FF = getvalue(𝒞) isa CSetCat ? FinFunction : left
  NamedTuple(sort(map(collect(pairs(components(hom(A))))) do (k,vs) 
    k => Subobject(k ∈ ob(S) ? vs : FF(vs))
  end; by=first))
end

force(A::SubACSet) = Subobject(force(hom(A)))

""" Sub-C-set represented componentwise as a collection of subsets.
"""
@struct_hash_equal struct SubACSetComponentwise{
    Ob<:ACSet, Comp<:NamedTuple} <: Subobject{Ob}
  ob::Ob
  components::Comp

  function SubACSetComponentwise(X::Ob, components::NamedTuple; cat=nothing) where Ob<:ACSet
    S = acset_schema(X)
    cat = isnothing(cat) ? infer_acset_cat(X) : cat
    X_sets = NamedTuple(c => FinSet(get_ob(cat,X,c)) for c in types(S))
    keys(components) ⊆ keys(X_sets) || error(
      "$(keys(components)) ⊈ $(keys(X_sets))")
    coerced_components = NamedTuple{keys(X_sets)}(
      coerce_subob_component(set, get(components, ob, 1:0))
      for (ob, set) in pairs(X_sets))
    new{Ob,typeof(coerced_components)}(X, coerced_components)
  end
end

Subobject(X::ACSet, components::NamedTuple) =
  SubACSetComponentwise(X, components)
Subobject(X::ACSet; components...) = Subobject(X, (; components...))

function coerce_subob_component(X::FinSet, subset::SubFinSet)
  X == ob(subset) ? subset :
    error("Set $X in C-set does not match set of subset $subset")
end
function coerce_subob_component(X::FinSet, f::FinFunction)
  X == codom(f) ? Subobject(f) :
    error("Set $X in C-set does not match codomain of inclusion $f")
end

coerce_subob_component(X::FinSet, f) = Subobject(X, f)

ob(A::SubACSetComponentwise) = A.ob
components(A::SubACSetComponentwise) = NamedTuple(sort(collect(
  pairs(A.components)); by=first))

function hom(A::SubACSetComponentwise{T}) where T <: ACSet
  X = ob(A)
  U = constructor(X)()
  hom_components = map(collect∘hom, components(A))
  copy_parts!(U, X, hom_components)
  ACSetTransformation(U, X; Dict(map(collect(pairs(hom_components))) do (k,vs)
    k => k ∈ ob(acset_schema(X)) ? vs : AttrVar.(vs)
  end)...)
end

# TODO: this just uses `SubobjectElementWise` instead of the limits and 
# colimits model, so this will fail for most ACSet types.
@instance ThSubobjectBiHeytingAlgebra{ACSet,SubACSet} [model::ACSetCategory] begin
  function meet(A::SubACSet, B::SubACSet)
    Subobject(common_ob(A, B), map(components(A), components(B)) do A₀, B₀
      meet[SubobjectElementWise()](A₀, B₀)
    end)
  end
  function join(A::SubACSet, B::SubACSet)
    Subobject(common_ob(A, B), map(components(A), components(B)) do A₀, B₀
      join[SubobjectElementWise()](A₀, B₀)
    end)
  end
  top(X::ACSet) =
    Subobject(X, map(X₀ -> top[SubobjectElementWise()](X₀), sets(X)))
  bottom(X::ACSet) =
    Subobject(X, map(X₀ -> bottom[SubobjectElementWise()](X₀), sets(X)))


    """ Implication of sub-C-sets.

    By (Reyes et al 2004, Proposition 9.1.5), the implication ``A ⟹ B`` for two
    sub-``C``-sets ``A,B ↪ X`` is given by
    
    ``x ∈ (A ⟹ B)(c) iff ∀f: c → c′, x⋅f ∈ A(c′) ⟹ x⋅f ∈ B(c′)``
    
    for all ``c ∈ C`` and ``x ∈ X(c)``. By the definition of implication and De
    Morgan's law in classical logic, this is equivalent to
    
    ``x ∉ (A ⟹ B)(c) iff ∃f: c → c′, x⋅f ∈ A(c′) ∧ x⋅f ∉ B(c′)``.
    
    In this form, we can clearly see the duality to formula and algorithm for
    subtraction of sub-C-sets ([`subtract`](@ref)).
    """
    function implies(A::SubACSet, B::SubACSet)
      X = common_ob(A, B)
      S = acset_schema(X)
      A, B = map(predicate, components(A)), map(predicate, components(B))
      D = NamedTuple([o => trues(nparts(X, o)) for o in types(S)])
      function unset!(c, x)
        D[c][x] = false
        for (c′,x′) in all_incident(X, Val{c}, x)
          if D[c′][x′]; unset!(c′,x′) end
        end
      end
    
      for c in types(S), x in parts(X,c)
        if D[c][x] && A[c][x] && !B[c][x]; unset!(c,x) end
      end
      Subobject(X, D)
    end
    
    """ Subtraction of sub-C-sets.
    
    By (Reyes et al 2004, Sec 9.1, pp. 144), the subtraction ``A ∖ B`` for two
    sub-``C``-sets ``A,B ↪ X`` is given by
    
    ``x ∈ (A ∖ B)(c) iff ∃f: c′ → c, ∃x′ ∈ f⁻¹⋅x, x′ ∈ A(c′) ∧ x′ ∉ B(c′)``
    
    for all ``c ∈ C`` and ``x ∈ X(c)``. Compare with [`implies`](@ref).
    """
    function subtract(A::SubACSet, B::SubACSet)
      X = common_ob(A, B)
      S = acset_schema(X)
      A, B = map(predicate, components(A)), map(predicate, components(B))
      D = NamedTuple(o => falses(nparts(X, o)) for o in types(S))
    
      set!(c::Symbol, x::AttrVar) = D[c][x.val] = true
      function set!(c::Symbol, x::Int)
        D[c][x] = true
        for (c′,x′) in all_subparts(X, Val{c}, x)
          if (c′ ∈ ob(S) && !D[c′][x′]) || x′ isa AttrVar 
            set!(c′,x′) 
          end
        end
      end
    
      for c in types(S), x in parts(X,c)
        if !D[c][x] && A[c][x] && !B[c][x]; set!(c,x) end
      end
      Subobject(X, D)
    end
    

  negate(A::SubACSet) = implies[model](A, bottom[model](ob(A)))
    
  non(A::SubACSet) = subtract[model](top[model](ob(A)), A)
end


function common_ob(A::Subobject, B::Subobject)
  (X = ob(A)) == ob(B) ||
    error("Subobjects have different base objects: $(ob(A)) != $(ob(B))")
  return X
end

# FIXME: Should these two accessors go elsewhere?

@generated function all_subparts(X::StructACSet{S},
                                 ::Type{Val{c}}, x::Int) where {S,c}
  Expr(:tuple, map(arrows(S; from=c)) do (f,_,c′)
    :($(quot(c′)), subpart(X,x,$(quot(f))))
  end...)
end

@generated function all_incident(X::StructACSet{S},
                                 ::Type{Val{c}}, x::Int) where {S,c}
  Expr(:call, GlobalRef(Iterators, :flatten),
    Expr(:tuple, map(homs(S; to=c)) do (f,c′,_)
      :(Tuple{Symbol,Int}[ ($(quot(c′)),x′) for x′ in incident(X,x,$(quot(f))) ])
    end...))
end


"""A map f (from A to B) as a map of subobjects of A to subjects of B"""
(f::ACSetTransformation)(X::SubACSet) = begin
  ob(X) == dom(f) || error("Cannot apply $f to $X")
  Subobject(codom(f); Dict(map(ob(acset_schema(dom(f)))) do o
    o => sort(unique(f[o].(collect(components(X)[o]))))
  end)...)
end


"""
A map f (from A to B) as a map from A to a subobject of B
# i.e. get the image of f as a subobject of B
"""
(f::ACSetTransformation)(X::StructACSet) =
  X == dom(f) ? f(top[infer_acset_cat(X)](X)) : error("Cannot apply $f to $X")

"""    preimage(f::ACSetTransformation,Y::Subobject)
Inverse of f (from A to B) as a map of subobjects of B to subjects of A.
"""
function preimage(f::ACSetTransformation,Y::SubACSet)
  ob(Y) == codom(f) || error("Cannot apply $f to $X")
  S = acset_schema(dom(f))
  Subobject(dom(f); Dict{Symbol, Vector{Int}}(map(ob(S)) do o
    o => sort(unique(vcat([preimage(f[o],y) 
                           for y in collect(components(Y)[o])]...)))
  end)...)
end

"""    preimage(f::ACSetTransformation,Y::StructACSet)
Inverse f (from A to B) as a map from subobjects of B to subobjects of A.
Cast an ACSet to subobject, though this has a trivial answer when computing
the preimage (it is necessarily the top subobject of A).
"""
preimage(f::ACSetTransformation,Y::StructACSet) =
  Y == codom(f) ? top[infer_acset_cat(Y)](dom(f)) : error(
    "Cannot apply inverse of $f to $Y")

end # module
