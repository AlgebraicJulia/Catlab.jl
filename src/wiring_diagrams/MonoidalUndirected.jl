""" Undirected wiring diagrams as symmetric monoidal categories.
"""
module MonoidalUndirectedWiringDiagrams
export cospan_action

import ...Theories: otimes, ⊗
using ...CategoricalAlgebra.CSets: disjoint_union
using ..UndirectedWiringDiagrams

const AbstractUWD = UndirectedWiringDiagram

# Cospan algebra
################

otimes(f::T, g::T) where T <: AbstractUWD = disjoint_union(f, g)
⊗(f::T, g::T) where T <: AbstractUWD = otimes(f, g)

""" Act on undirected wiring diagram with a cospan, as in a cospan algebra.

A *cospan algebra* is a lax monoidal functor from a category of (typed) cospans
(Cospan,⊕) to (Set,×) (Fong & Spivak, 2019, Hypergraph categories, §2.1: Cospans
and cospan-algebras). Undirected wiring diagrams are a cospan algebra in
essentially the same way that any hypergraph category is (Fong & Spivak, 2019,
§4.1: Cospan-algebras and hypergraph categories are equivalent). In fact, we use
this action to implement the hypergraph category structure, particularly
composition, on undirected wiring diagrams.
"""
function cospan_action(f::AbstractUWD, args...)
  ocompose(cospan_diagram(typeof(f), args...), 1, f)
end

end
