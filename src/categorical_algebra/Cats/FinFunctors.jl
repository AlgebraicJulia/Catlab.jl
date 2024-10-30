module FinFunctors 
export FinFunctor, FinDomFunctor, is_functorial, functoriality_failures,
        collect_ob, collect_hom, force, make_map,
        FinTransformation, components, is_natural, is_initial,dom_to_graph

using DataStructures: IntDisjointSets, in_same_set, num_groups
using StructEquality
using GATlab

using ....Theories: ObExpr, HomExpr, AttrExpr
using ..FinCats, ..Categories
using ..Categories: AbsCat, AbsFunctorImpl, ThFunctor
# using ..FinCats: 

# Functors
##########

abstract type FinDomFunctorImpl{DO,CO,DH,CH,DG,CG,DC<:FinCat{DO,DH,DG},
  CC<:AbsCat{CO,CH}} <: AbsFunctorImpl{DO,CO,DH,CH,DG,CG,DC,CC} end 
  
""" A functor out of a finitely-presented category.
"""
const FinDomFunctor{DO,CO,DH,CH,DG,CG,DC<:FinCat{DO,DH,DG},CC<:AbsCat{CO,CH}} = 
  Functor{DO,CO,DH,CH,DG,CG,DC,CC}

""" A functor between finitely-presented categories.
"""
const FinFunctor{DO,CO,DH,CH,DG,CG,DC<:FinCat{DO,DH,DG},CC<:FinCat{CO,CH,CG}} = 
  Functor{DO,CO,DH,CH,DG,CG,DC,CC}

# # Mapping-based functors
# #-----------------------

""" View Vectors equivalently as Int-keyed Dictionaries """
const VD{K,V} = Union{AbstractVector{V},AbstractDict{K,V}}

""" Functor out of a finitely presented category given by explicit mappings.
"""
@struct_hash_equal struct FinDomFunctorMap{DO,CO,DH,CH,DG,CG,
    Dom<:FinCat{DO,DH,DG}, Codom<:AbsCat{CO,CH}, ObMap, HomMap
    } <: FinDomFunctorImpl{DO,CO,DH,CH,DG,CG,Dom,Codom}
  ob_map::ObMap
  hom_map::HomMap
  dom::Dom
  codom::Codom
end

""" Construct FinDomFunctorMap from two vectors """
FinDomFunctorMap(om::OM, hm::HM, d::D, c::C
                ) where {DH,CO,CH,CG,OM<:AbstractVector{<:CO}, 
                         HM<:AbstractVector{<:CH},D<:FinCat{Int,DH,Int},
                         C<:FinCat{CO,CH,CG}} = 
  FinDomFunctorMap{Int,CO,DH,CH,Int,CG,D,C,OM,HM}(om,hm,d,c)

""" 
Construct FinDomFunctorMap from two vectors. Hom vector given in terms of 
codom generators. 
"""
function FinDomFunctorMap(om::OM, hm::HM, d::D, c::C
                ) where {DH,CO,CH,CG,OM<:AbstractVector{<:CO}, 
                         HM<:AbstractVector{<:AbstractVector{<:CG}},
                         D<:FinCat{Int,DH,Int},
                         C<:FinCat{CO,CH,CG}} 
  v= CH[compose(c, h) for h in hm]
  FinDomFunctorMap{Int,CO,DH,CH,Int,CG,D,C,OM,typeof(v)}(om,v,d,c)
end 
""" Construct FinDomFunctorMap from two dictionaries """
FinDomFunctorMap(om::OM, hm::HM, d::D, c::C
                ) where {DO,DH,DG,CO,CH,CG,OM<:AbstractDict{<:DO,<:CO}, 
                         HM<:AbstractDict{<:DG,<:CH},D<:FinCat{DO,DH,DG},
                         C<:FinCat{CO,CH,CG}} = 
  FinDomFunctorMap{DO,CO,DH,CH,DG,CG,D,C,OM,HM}(om,hm,d,c)

@instance ThFunctor{DO,CO,DH,CH,DG,CG,CC,DC
                   } [model::FinDomFunctorMap{DO,CO,DH,CH,DG,CG,CC,DC,OM,HM}
                     ] where {DO,CO,DH,CH,DG,CG,CC,DC,OM,HM} begin 
  dom() = model.dom

  codom() = model.codom

  ob_map(x::DO) = model.ob_map[x]  

  hom_map(f::DG) = model.hom_map[f]
end

function FinDomFunctor(ob_map::Union{<:AbstractVector,<:AbstractDict}, 
                       hom_map::Union{<:AbstractVector,<:AbstractDict},
                       dom::FinCat{DO,DH,DG}, 
                       codom::Union{AbsCat{CO,CH},Nothing}=nothing
                       ) where {DO,DH,DG,CO,CH}
  length(ob_map) == length(ob_generators(dom)) ||
    error("Length of object map $ob_map does not match domain $dom")
  length(hom_map) == length(hom_generators(dom)) ||
    error("Length of morphism map $hom_map does not match domain $dom")
  # NOTE: removed the empty checks which avoid Julia blowing up the type
  codom = isnothing(codom) ? Cat(TypeCat{CO,CH}()) : codom
  FinDomFunctorMap(ob_map, hom_map, dom, codom) |> Functor
end


FinDomFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCat, codom::AbsCat) =
  if getvalue(dom) isa FinCatGraph 
    FinDomFunctor(maps.V, maps.E, dom, codom)
  else 
    error("bad maps $maps for dom $dom")
  end

function FinDomFunctor(ob_map, dom::FinCat, codom::AbsCat{Ob,Hom}) where {Ob,Hom}
  is_discrete(dom) ||
    error("Morphism map omitted by domain category is not discrete: $dom")
  FinDomFunctor(FinDomFunctorMap(ob_map, empty(ob_map, Hom), dom, codom))
end

FinDomFunctor(ob_map, ::Nothing, dom::FinCat, codom::AbsCat) =
  FinDomFunctor(ob_map, dom, codom)

function hom_map(F::FinDomFunctor{<:Any,<:Any,H,<:Any,G}, path::H) where {H,G}
  C, D = dom(F), codom(F)
  path = decompose(getvalue(C), path)
  mapreduce(e -> hom_map(F, e), (gs...) -> compose(D, gs...),
             edges(path), init=id(D, ob_map(F, dom(C, path))))
end


function hom_map(F::FinDomFunctor, f::GATExpr{:compose})
  C, D = dom(F), codom(F)
  mapreduce(f -> hom_map(F, f), (gs...) -> compose(D, gs...), decompose(C, f))
end

function hom_map(F::FinDomFunctor, f::GATExpr{:id})
  id(codom(F), ob_map(F, dom(f)))
end

(F::FinDomFunctor)(expr::ObExpr) = ob_map(F, expr)
(F::FinDomFunctor)(expr::HomExpr) = hom_map(F, expr)

Categories.show_type_constructor(io::IO, ::Type{<:FinDomFunctor}) =
  print(io, "FinDomFunctor")

""" Collect assignments of functor's object map as a vector.
"""
collect_ob(F::FinDomFunctor) = map(x -> ob_map(F, x), ob_generators(dom(F)))

""" Collect assignments of functor's morphism map as a vector.
"""
collect_hom(F::FinDomFunctor) = map(f -> hom_map(F, f), hom_generators(dom(F)))

""" Is the purported functor on a presented category functorial?

This function checks that functor preserves domains and codomains. When
`check_equations` is `true` (the default is `false`), it also purports to check
that the functor preserves all equations in the domain category. No nontrivial 
checks are currently implemented, so this only functions for identity functors.

See also: [`functoriality_failures'](@ref) and [`is_natural`](@ref).
"""
function is_functorial(F::FinDomFunctor; kw...)
  failures = functoriality_failures(F; kw...)
  all(isempty, failures)
end

""" Failures of the purported functor on a presented category to be functorial.

Similar to [`is_functorial`](@ref) (and with the same caveats) but returns
iterators of functoriality failures: one for domain incompatibilities, one for
codomain incompatibilities, and one for equations that are not satisfied.
"""
function functoriality_failures(F::FinDomFunctor; check_equations::Bool=false)
  C, D = dom(F), codom(F)
  bad_dom = Iterators.filter(hom_generators(C)) do f 
    dom(D, hom_map(F, f)) != ob_map(F, dom(C,f))
  end 
  bad_cod = Iterators.filter(hom_generators(C)) do f 
    codom(D, hom_map(F, f)) != ob_map(F, codom(C,f))
  end
  bad_eqs = if check_equations
    # TODO: Currently this won't check for nontrivial equalities
    Iterators.filter(equations(C)) do (lhs,rhs)
      !is_hom_equal(D,hom_map(F,lhs),hom_map(F,rhs))
    end
  else () end
  (bad_dom, bad_cod, bad_eqs)
end

function Base.map(F::Functor{<:FinCat,<:TypeCat}, f_ob, f_hom)
  C = dom(F)
  FinDomFunctor(map(x -> f_ob(ob_map(F, x)), ob_generators(C)),
                map(f -> f_hom(hom_map(F, f)), hom_generators(C)), C)
end




FinFunctor(maps, dom::FinCat, codom::FinCat) = FinDomFunctor(maps, dom, codom)

FinFunctor(ob_map, hom_map, dom::FinCat, codom::FinCat) =
  FinDomFunctor(ob_map, hom_map, dom, codom)

FinFunctor(ob_map, hom_map, dom::Presentation, codom::Presentation) =
  FinDomFunctor(ob_map, hom_map, FinCat(dom), FinCat(codom))

Categories.show_type_constructor(io::IO, ::Type{<:FinFunctor}) =
  print(io, "FinFunctor")

# Dict utilities
################

# Something like this should be built into Julia, but unfortunately isn't.

"""
Map two given functions across the respective keys and values of a dictionary.
"""
function mappairs(kmap, vmap, pairs::T;fixkeytype=false,fixvaltype=false) where {K,V,T<:AbstractDict{K,V}}
  S = dicttype(T)
  d = S(kmap(k) => vmap(v) for (k,v) in pairs)
  R = fixvaltype ? fixkeytype ? T : S{keytype(d),V} :
      fixkeytype ? S{K} : S
  R(d)
end
#XX:might want to add fixtype to here sometime
mappairs(kmap, vmap, vec::AbstractVector;kw...) = map(vmap, vec)


"""
Map a function, which may depend on the key, across the values of a dictionary.
"""
function mapvals(f, pairs::T; keys::Bool=false, iter::Bool=false) where T<:AbstractDict
  (iter ? identity : dicttype(T))(if keys
    (k => f(k,v) for (k,v) in pairs)
  else
    (k => f(v) for (k,v) in pairs)
  end)
end
function mapvals(f, collection; keys::Bool=false, iter::Bool=false)
  do_map = iter ? Iterators.map : map
  if keys
    do_map(f, eachindex(collection), values(collection))
  else
    do_map(f, values(collection))
  end
end

dicttype(::Type{T}) where T <: AbstractDict = T.name.wrapper
dicttype(::Type{<:Iterators.Pairs}) = Dict

@inline make_map(f, xs) = make_map(f, xs, Any)

"""
Maps `f` over a `UnitRange` to produce a `Vector`,
or else over anything to produce a `Dict`. The type paramter
functions to ensure the return type is as desired even when the
input is empty.
"""
function make_map(f, xs::UnitRange{Int}, ::Type{T}) where T
  if isempty(xs)
    T[]
  else
    ys = map(f, xs)
    eltype(ys) <: T || error("Element(s) of $ys are not instances of $T")
    ys
  end
end

function make_map(f, xs, ::Type{T}) where T
  if isempty(xs)
    Dict{eltype(xs),T}()
  else
    xys = Dict(x => f(x) for x in xs)
    valtype(xys) <: T || error("Value(s) of $xys are not instances of $T")
    xys
  end
end

# # Symbolic categories
# #####################


# # Functors
# ##########


# ob_key(C::FinCat, x) = ob_generator(C, x)
# hom_key(C::FinCat, f) = hom_generator(C, f)
# ob_map(F::FinDomFunctorMap) = F.ob_map
# hom_map(F::FinDomFunctorMap) = F.hom_map

# ob_key(C::OppositeFinCat, x) = ob_key(C.cat,x)
# hom_key(C::OppositeFinCat, f) = hom_key(C.cat,f)

# Categories.do_ob_map(F::FinDomFunctorMap, x) = F.ob_map[ob_key(F.dom, x)]
# Categories.do_hom_map(F::FinDomFunctorMap, f) = F.hom_map[hom_key(F.dom, f)]

# collect_ob(F::FinDomFunctorMap) = collect_values(F.ob_map)
# collect_hom(F::FinDomFunctorMap) = collect_values(F.hom_map)
# collect_values(vect::AbstractVector) = vect
# collect_values(dict::AbstractDict) = collect(values(dict))

# op(F::FinDomFunctorMap) = FinDomFunctorMap(F.ob_map, F.hom_map,
#                                            op(dom(F)), op(codom(F)))

# """ Force evaluation of lazily defined function or functor.
# The resulting ob_map and hom_map are guaranteed to have 
# valtype or eltype, as appropriate, equal to Ob and Hom,
# respectively. 
# """
# function force(F::FinDomFunctor, Obtype::Type=Any, Homtype::Type=Any)
#   C = dom(F)
#   FinDomFunctor(
#     make_map(x -> ob_map(F, x), ob_generators(C), Obtype),
#     make_map(f -> hom_map(F,f), hom_generators(C), Homtype), 
#     C)
# end

# function Categories.do_compose(F::FinDomFunctorMap, G::FinDomFunctorMap)
#   FinDomFunctor(mapvals(x -> ob_map(G, x), F.ob_map),
#                    mapvals(f -> hom_map(G, f), F.hom_map), dom(F), codom(G))
# end

# diagram_type(F::FinDomFunctor{Dom,Codom}) where {Ob,Hom,Dom,Codom<:Cat{Ob,Hom}} =
#   Tuple{Ob,Hom}

# cone_objects(F::FinDomFunctor) = collect_ob(F)

# cocone_objects(F::FinDomFunctor) = collect_ob(F)

# function FreeDiagram(F::FinDomFunctor{Dom,Codom}) where {Ob,Hom,Dom,Codom<:Cat{Ob,Hom}} 
#   C = dom(F)
#   diagram = FreeDiagram{Ob,Hom}()
#   ob_dict = Dict(map(ob_generators(C)) do x 
#     x => add_vertex!(diagram; ob=ob_map(F, x))
#   end)
#   for h in hom_generators(C)
#     add_edge!(diagram, ob_dict[dom(C,h)], ob_dict[codom(C,h)], hom=hom_map(F,h))
#   end
#   diagram 
# end

# """ Wrapper type to interpret `FreeDiagram` as a `FinDomFunctor`.
# """
# @struct_hash_equal struct FreeDiagramFunctor{Ob,Hom,Codom} <:
#     FinDomFunctor{FreeCatGraph{AbstractFreeDiagram{<:Any,Tuple{Ob,Hom}}},Codom}
#   diagram::FreeDiagram{Ob,Hom}
#   codom::Codom
# end

# FinDomFunctor(diagram::FreeDiagram, codom::Cat) =
#   FreeDiagramFunctor(diagram, codom)

# FinDomFunctor(diagram::FreeDiagram{Ob,Hom}) where {Ob,Hom} =
#   FreeDiagramFunctor(diagram, TypeCat(Ob, Hom))

# dom(F::FreeDiagramFunctor) = FreeCatGraph(getvalue(F.diagram))

# Categories.do_ob_map(F::FreeDiagramFunctor, x) = ob(F.diagram, x)

# Categories.do_hom_map(F::FreeDiagramFunctor, f) = hom(F.diagram, f)

# collect_ob(F::FreeDiagramFunctor) = ob(F.diagram)

# collect_hom(F::FreeDiagramFunctor) = hom(F.diagram)


# """
# Reinterpret a functor on a finitely presented category
# as a functor on the equivalent category (ignoring equations)
# free on a graph. Also normalizes the input to have vector ob_map
# and hom_map, with valtype optionally specified. This is useful when
# the domain is empty or when the maps might be tightly typed but need to
# allow for types such as that of identity morphisms upon mutation.
# """
# function dom_to_graph(F::FinDomFunctor{Dom,<:Cat{Ob,Hom}},obtype=Ob,homtype=Hom) where {Dom,Ob,Hom} 
#   D = dom(F)
#   C = FinCat(graph(D))
#   new_obs = obtype[ob_map(F,ob) for ob in ob_generators(D)]
#   new_homs = homtype[hom_map(F,hom) for hom in hom_generators(D)]
#   FinDomFunctorMap(new_obs,new_homs,C,TypeCat(obtype,homtype))
# end

# function Base.show(io::IO, F::T) where T <: FinDomFunctorMap
#   Categories.show_type_constructor(io, T); print(io, "(")
#   show(io, F.ob_map)
#   print(io, ", ")
#   show(io, F.hom_map)
#   print(io, ", ")
#   Categories.show_domains(io, F)
#   print(io, ")")
# end

# # Natural transformations
# #########################

# """ A natural transformation whose domain category is finitely generated.

# This type is for natural transformations ``α: F ⇒ G: C → D`` such that the
# domain category ``C`` is finitely generated. Such a natural transformation is
# given by a finite amount of data (one morphism in ``D`` for each generating
# object of ``C``) and its naturality is verified by finitely many equations (one
# equation for each generating morphism of ``C``).
# """
# const FinTransformation{C<:FinCat,D<:Cat,Dom<:FinDomFunctor,Codom<:FinDomFunctor} =
#   Transformation{C,D,Dom,Codom}

# FinTransformation(F, G; components...) = FinTransformation(components, F, G)

# """ Components of a natural transformation.
# """
# components(α::FinTransformation) =
#   make_map(x -> component(α, x), ob_generators(dom_ob(α)))

# """ Is the transformation between `FinDomFunctors` a natural transformation?

# This function uses the fact that to check whether a transformation is natural,
# it suffices to check the naturality equations on a generating set of morphisms
# of the domain category. In some cases, checking the equations may be expensive
# or impossible. When the keyword argument `check_equations` is `false`, only the
# domains and codomains of the components are checked.

# See also: [`is_functorial`](@ref).
# """
# function is_natural(α::FinTransformation; check_equations::Bool=true)
#   F, G = dom(α), codom(α)
#   C, D = dom(F), codom(F) # == dom(G), codom(G)
#   all(ob_generators(C)) do c
#     α_c = α[c]
#     dom(D, α_c) == ob_map(F,c) && codom(D, α_c) == ob_map(G,c)
#   end || return false

#   if check_equations
#     all(hom_generators(C)) do f
#       Ff, Gf = hom_map(F,f), hom_map(G,f)
#       α_c, α_d = α[dom(C,f)], α[codom(C,f)]
#       is_hom_equal(D, compose(D, α_c, Gf), compose(D, Ff, α_d))
#     end || return false
#   end

#   true
# end

# function check_transformation_domains(F::Functor, G::Functor)
#   # XXX: Equality of TypeCats is too strict, so for now we are punting on
#   # (co)domain checks in that case.
#   C, C′ = dom(F), dom(G)
#   (C isa TypeCat && C′ isa TypeCat) || C == C′ ||
#     error("Mismatched domains in functors $F and $G")
#   D, D′ = codom(F), codom(G)
#   (D isa TypeCat && D′ isa TypeCat) || D == D′ ||
#     error("Mismatched codomains in functors $F and $G")
#   (C, D)
# end

# # Mapping-based transformations
# #------------------------------

# """ Natural transformation with components given by explicit mapping.
# """
# @struct_hash_equal struct FinTransformationMap{C<:FinCat,D<:Cat,
#     Dom<:FinDomFunctor{C,D},Codom<:FinDomFunctor,Comp} <: FinTransformation{C,D,Dom,Codom}
#   components::Comp
#   dom::Dom
#   codom::Codom
# end

# function FinTransformation(components::Union{AbstractVector,AbstractDict},
#                            F::FinDomFunctor, G::FinDomFunctor)
#   C, D = check_transformation_domains(F, G)
#   length(components) == length(ob_generators(C)) ||
#     error("Incorrect number of components in $components for domain category $C")
#   components = mappairs(x -> ob_key(C,x), f -> hom(D,f), components)
#   FinTransformationMap(components, F, G)
# end

# component(α::FinTransformationMap, x) = α.components[ob_key(dom_ob(α), x)]
# components(α::FinTransformationMap) = α.components

# op(α::FinTransformationMap) = FinTransformationMap(components(α),
#                                                    op(codom(α)), op(dom(α)))

# function Categories.do_compose(α::FinTransformationMap, β::FinTransformation)
#   F = dom(α)
#   D = codom(F)
#   FinTransformationMap(mapvals(α.components, keys=true) do c, f
#                          compose(D, f, component(β, c))
#                        end, F, codom(β))
# end

# function Categories.do_composeH(F::FinDomFunctorMap, β::Transformation)
#   G, H = dom(β), codom(β)
#   FinTransformationMap(mapvals(c -> component(β, c), F.ob_map),
#                        compose(F, G), compose(F, H))
# end

# function Categories.do_composeH(α::FinTransformationMap, H::Functor)
#   F, G = dom(α), codom(α)
#   FinTransformationMap(mapvals(f->hom_map(H,f),α.components),
#                       compose(F, H), compose(G, H))
# end

# function Base.show(io::IO, α::FinTransformationMap)
#   print(io, "FinTransformation(")
#   show(io, components(α))
#   print(io, ", ")
#   Categories.show_domains(io, α, recurse=false)
#   print(io, ", ")
#   Categories.show_domains(io, dom(α))
#   print(io, ")")
# end

# # Initial functors
# ##################

# """
# Dual to a [final functor](https://ncatlab.org/nlab/show/final+functor), an
# *initial functor* is one for which pulling back diagrams along it does not
# change the limits of these diagrams.

# This amounts to checking, for a functor C->D, that, for every object d in
# Ob(D), the comma category (F/d) is connected.
# """
# function is_initial(F::FinFunctor)::Bool
#   Gₛ, Gₜ = graph(dom(F)), graph(codom(F))
#   pathₛ, pathₜ = enumerate_paths.([Gₛ, Gₜ])

#   function connected_nonempty_slice(t::Int)::Bool
#     paths_into_t = incident(pathₜ, t, :tgt)
#     # Generate slice objects
#     ob_slice = Pair{Int,Vector{Int}}[] # s ∈ Ob(S) and a path ∈ T(F(s), t)
#     for s in vertices(Gₛ)
#       paths_s_to_t = incident(pathₜ, ob_map(F,s), :src) ∩ paths_into_t
#       append!(ob_slice, [s => pathₜ[p, :eprops] for p in paths_s_to_t])
#     end

#     # Empty case
#     isempty(ob_slice) && return false

#     """
#     For two slice objects (m,pₘ) and (n,pₙ) check for a morphism f ∈ S(M,N) such
#     that there is a commutative triangle pₘ = f;pₙ
#     """
#     function check_pair(i::Int, j::Int)::Bool
#       (m,pₘ), (n,pₙ) = ob_slice[i], ob_slice[j]
#       es = incident(pathₛ, m, :src) ∩ incident(pathₛ, n, :tgt)
#       paths = pathₛ[es, :eprops]
#       return any(f -> pₘ == vcat(edges.(hom_map(F,f))..., pₙ), paths)
#     end

#     # Use check_pair to determine pairwise connectivity
#     connected = IntDisjointSets(length(ob_slice)) # sym/trans/refl closure
#     obs = 1:length(ob_slice)
#     for (i,j) in Base.Iterators.product(obs, obs)
#       if !in_same_set(connected, i, j) && check_pair(i,j)
#         union!(connected, i, j)
#       end
#     end
#     return num_groups(connected) == 1
#   end

#   # Check for each t ∈ T whether F/t is connected
#   return all(connected_nonempty_slice, 1:nv(Gₜ))
# end


end # module