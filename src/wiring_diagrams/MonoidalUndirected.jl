""" Undirected wiring diagrams as symmetric monoidal categories.
"""
module MonoidalUndirectedWiringDiagrams
export HypergraphDiagram, HypergraphDiagramOb, HypergraphDiagramHom,
  ObUWD, HomUWD, cospan_action, dom_mask, codom_mask

using AutoHashEquals
using Compat: isnothing

using ...GAT, ...Present, ...CategoricalAlgebra.CSets
using ...Theories: HypergraphCategory
import ...Theories: dom, codom, compose, id, ⋅, ∘, otimes, ⊗, munit, braid, σ,
  mcopy, Δ, mmerge, ∇, delete, ◊, create, □, dunit, dcounit, dagger
using ...CategoricalAlgebra.CSets: disjoint_union
using ..UndirectedWiringDiagrams
using ..UndirectedWiringDiagrams: AbstractUWD, TheoryUWD, TheoryTypedUWD
import ..UndirectedWiringDiagrams: singleton_diagram, junction_diagram

# Data types
############

@present TheoryUntypedHypergraphDiagram <: TheoryUWD begin
  Name::Data
  name::Attr(Box,Name)
end

const UntypedHypergraphDiagram = ACSetType(TheoryUntypedHypergraphDiagram,
  index=[:box, :junction, :outer_junction])

""" Diagram suitable for representing morphisms in hypergraph categories.

An undirected wiring diagram where the ports and junctions are typed and the
boxes have names identifying the morphisms.
"""
@present TheoryHypergraphDiagram <: TheoryTypedUWD begin
  Name::Data
  name::Attr(Box,Name)
end

const HypergraphDiagram = ACSetType(TheoryHypergraphDiagram,
  index=[:box, :junction, :outer_junction])

# Cospan algebra
################

""" Act on undirected wiring diagram with a cospan, as in a cospan algebra.

A *cospan algebra* is a lax monoidal functor from a category of (typed) cospans
(Cospan,⊕) to (Set,×) (Fong & Spivak, 2019, Hypergraph categories, §2.1: Cospans
and cospan-algebras). Undirected wiring diagrams are a cospan algebra in
essentially the same way that any hypergraph category is (Fong & Spivak, 2019,
§4.1: Cospan-algebras and hypergraph categories are equivalent). In fact, we use
this action to implement the hypergraph category structure, particularly
composition, on undirected wiring diagrams.
"""
function cospan_action(f::UWD, args...) where UWD <: AbstractUWD
  ocompose(cospan_diagram(UWD, args...), 1, f)
end

function compose(f::UWD, g::UWD,
                 f_codom::BitVector, g_dom::BitVector) where UWD <: AbstractUWD
  f_dom, g_codom = .!f_codom, .!g_dom
  k, ℓ, ℓ′, m = sum(f_dom), sum(f_codom), sum(g_dom), sum(g_codom)
  @assert ℓ == ℓ′
  f_inner, g_inner = zeros(Int, k+ℓ), zeros(Int, ℓ+m)
  f_inner[f_dom] = 1:k; g_inner[g_codom] = k+ℓ .+ (1:m)
  f_inner[f_codom] = g_inner[g_dom] = k .+ (1:ℓ)
  inner, outer = [f_inner; g_inner], [1:k; k+ℓ .+ (1:m)]
  junction_types = [ port_type(f, f_dom, outer=true);
                     port_type(f, f_codom, outer=true);
                     port_type(g, g_codom, outer=true) ]
  cospan_action(f⊗g, inner, outer, junction_types)
end

otimes(f::UWD, g::UWD) where UWD <: AbstractUWD = disjoint_union(f, g)
⊗(f::UWD, g::UWD) where UWD <: AbstractUWD = otimes(f, g)

# Categorical interface
#######################

""" List of port types representing outer boundary of undirected wiring diagram.
"""
@auto_hash_equals struct ObUWD{UWD <: AbstractUWD, T}
  types::Vector{T}
end
ObUWD{UWD}(types::Vector{T}) where {UWD<:AbstractUWD,T} = ObUWD{UWD,T}(types)

Base.length(A::ObUWD) = length(A.types)
Base.cat(A::ObUWD{UWD}, B::ObUWD{UWD}) where UWD =
  ObUWD{UWD}([A.types; B.types])

""" Undirected wiring diagram with specified domain and codomain.

The outer ports of the undirected wiring diagram are partitioned into domain and
codomain by masks (bit vectors).
"""
@auto_hash_equals struct HomUWD{UWD <: AbstractUWD}
  diagram::UWD
  dom::BitVector

  function HomUWD{UWD}(diagram::UWD;
      dom::Union{BitVector,Nothing}=nothing,
      codom::Union{BitVector,Nothing}=nothing) where UWD <: AbstractUWD
    if !(isnothing(dom) || isnothing(codom))
      @assert codom == .!dom "Domain and codomain masks must form partition"
    elseif !isnothing(codom)
      dom = .!codom
    elseif isnothing(dom)
      error("Must supply at least one of domain and codomain masks")
    end
    length(dom) == length(ports(diagram, outer=true)) ||
      error("Length of (co)domain masks must equal number of outer ports")
    new{UWD}(diagram, dom)
  end
end
HomUWD(diagram::UWD; kw...) where UWD <: AbstractUWD =
  HomUWD{UWD}(diagram; kw...)

dom_mask(f::HomUWD) = f.dom
codom_mask(f::HomUWD) = .!f.dom

const HypergraphDiagramOb{T,Name} = ObUWD{HypergraphDiagram{T,Name},T}
const HypergraphDiagramHom{T,Name} = HomUWD{HypergraphDiagram{T,Name}}

dom_ports(f::HomUWD) = ports(f.diagram, outer=true)[dom_mask(f)]
codom_ports(f::HomUWD) = ports(f.diagram, outer=true)[codom_mask(f)]
dom_port_types(f::HomUWD) = port_type(f.diagram, dom_ports(f), outer=true)
codom_port_types(f::HomUWD) = port_type(f.diagram, codom_ports(f), outer=true)

dom(f::HomUWD{UWD}) where UWD = ObUWD{UWD}(dom_port_types(f))
codom(f::HomUWD{UWD}) where UWD = ObUWD{UWD}(codom_port_types(f))

""" Undirected wiring diagrams as a hypergraph category.

The objects are lists of port types and morphisms are undirected wiring diagrams
whose outer ports are partitioned into domain and codomain.
"""
@instance HypergraphCategory{ObUWD, HomUWD} begin
  @import dom, codom

  function compose(f::HomUWD, g::HomUWD)
    k, ℓ = sum(dom_mask(f)), sum(codom_mask(g))
    HomUWD(compose(f.diagram, g.diagram, codom_mask(f), dom_mask(g)),
           dom=(1:k+ℓ .<= k))
  end
  
  otimes(A::ObUWD, B::ObUWD) = cat(A, B)
  munit(::Type{ObUWD}) = ObUWD(Symbol[])

  function otimes(f::HomUWD, g::HomUWD)
    HomUWD(otimes(f.diagram, g.diagram), dom=[dom_mask(f); dom_mask(g)])
  end

  id(A::ObUWD) = let n = length(A)
    HomUWD(junction_diagram(A, repeat(1:n, 2)), dom=[trues(n); falses(n)])
  end
  braid(A::ObUWD, B::ObUWD) = let m = length(A), n = length(B)
    HomUWD(junction_diagram(A⊗B, [1:m+n; m+1:m+n; 1:m]),
           dom=[trues(m+n); falses(m+n)])
  end
  mcopy(A::ObUWD) = let n = length(A)
    HomUWD(junction_diagram(A, repeat(1:n, 3)), dom=[trues(n); falses(2n)])
  end
  mmerge(A::ObUWD) = let n = length(A)
    HomUWD(junction_diagram(A, repeat(1:n, 3)), dom=[trues(2n); falses(n)])
  end
  delete(A::ObUWD) = let n = length(A)
    HomUWD(junction_diagram(A, 1:n), dom=trues(n))
  end
  create(A::ObUWD) = let n = length(A)
    HomUWD(junction_diagram(A, 1:n), dom=falses(n))
  end
  dunit(A::ObUWD) = let n = length(A)
    HomUWD(junction_diagram(A, repeat(1:n, 2)), dom=falses(2n))
  end
  dcounit(A::ObUWD) = let n = length(A)
    HomUWD(junction_diagram(A, repeat(1:n, 2)), dom=trues(2n))
  end
  dagger(f::HomUWD) = HomUWD(f.diagram, codom=dom_mask(f))
end

munit(::Type{ObUWD{UWD}}) where UWD = ObUWD{UWD}(Symbol[])
munit(::Type{ObUWD{UWD,T}}) where {UWD,T} = ObUWD{UWD}(T[])

singleton_diagram(A::ObUWD{UWD}; data...) where UWD =
  singleton_diagram(UWD, A.types; data...)
junction_diagram(A::ObUWD{UWD}, outer) where UWD =
  junction_diagram(UWD, outer, A.types)

end
