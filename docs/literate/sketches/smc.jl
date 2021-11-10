# # Symmetric Monoidal Categories
# This vignette supports section 4.4.3 of Seven Sketches in Compositionality, which introduces the definition of symmetric monoidal categories (SMCs). SMCs are a core concept in applied category theory and are a workhorse of Catlab's utility in computing applications. We will discuss the definition as a GAT, see examples of working with formulas, and conversions to wiring diagrams (sometimes called string diagrams). 
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Catlab.Programs
using Catlab.WiringDiagrams

draw(d::WiringDiagram) = to_graphviz(d,
  orientation=LeftToRight,
  labels=true, label_attr=:xlabel,
  node_attrs=Graphviz.Attributes(
    :fontname => "Courier",
  ),
  edge_attrs=Graphviz.Attributes(
    :fontname => "Courier",
  )
)

# ## Definition
# Let 𝒞 be a category, then a strict symmetric monoidal structure on 𝒞 has as data:
# 1. An object I called the monoidal unit
# 2. A functor ⊗: 𝒞×𝒞 → 𝒞 called the monoidal product.
# 3. A natural isomorphism σᵃᵇ: A⊗B → B⊗A
#
# It has as axioms:
# 1. Left identity) I⊗C = C for all objects C in 𝒞
# 2. Right identity) C⊗I = C for all objects C in 𝒞
# 3. Associativity) (A⊗B)⊗C = A⊗(B⊗C) for all objects A,B,C in 𝒞
# 4. Involutivity) σ(σ(A,B)) = id(A⊗B) 
#
# If the SMC is not strict, then the equations are replaced by natural isomorphisms. The choice of natural isomorphisms then becomes part of the data of the SMC. With MacLane's coherence theorem for SMCs mathematicians can think about strict SMCs and not really worry too much about the natural isomorphisms. As programmers, those chickens come home to roost and implementing an SMC requires making some choices about about how to do that strictification. 
# 
# The Catlab definitions of SMC are repeated here for convenience. Catlab allows you to implement mathematical definitions in the language of Generalized Algebraic Theories (GATs), which are a good fit for the kind of natural language definitions that mathematicians will write. Because Catlab does relatively little type inference, the GAT version of a definition can be more verbose than you would get in natural language. For example, we have to be careful about spelling out the object for an identity morphism `id(A):A → A`. The notation  `@theory MonoidalCategory{Ob,Hom} <: Category{Ob,Hom}` says that a Monoidal Category is a type of Category with additional components and axioms. Catlab has only rudimentary support for Monoidal Categories that are not Symmetric Monoidal Categories. But we separate out the definitions for completeness.
# ```julia
# @theory MonoidalCategory{Ob,Hom} <: Category{Ob,Hom} begin
#   otimes(A::Ob, B::Ob)::Ob
#   otimes(f::(A → B), g::(C → D))::((A ⊗ C) → (B ⊗ D)) ⊣
#     (A::Ob, B::Ob, C::Ob, D::Ob)
#   @op (⊗) := otimes
#   munit()::Ob
#   # Monoid axioms.
#   #
#   # The last two axioms are the naturality equations associated with the left
#   # and right unitors, in the strict case where they are identities.
#   (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C) ⊣ (A::Ob, B::Ob, C::Ob)
#   munit() ⊗ A == A ⊣ (A::Ob)
#   A ⊗ munit() == A ⊣ (A::Ob)
#   (f ⊗ g) ⊗ h == f ⊗ (g ⊗ h) ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
#                                 f::(A → X), g::(B → Y), h::(C → Z))
#   id(munit()) ⊗ f == f ⊣ (A::Ob, B::Ob, f::(A → B))
#   f ⊗ id(munit()) == f ⊣ (A::Ob, B::Ob, f::(A → B))
#   # Functorality axioms.
#   ((f ⊗ g) ⋅ (h ⊗ k) == (f ⋅ h) ⊗ (g ⋅ k)
#     ⊣ (A::Ob, B::Ob, C::Ob, X::Ob, Y::Ob, Z::Ob,
#        f::(A → B), h::(B → C), g::(X → Y), k::(Y → Z)))
#   id(A ⊗ B) == id(A) ⊗ id(B) ⊣ (A::Ob, B::Ob)
# end
# ```
# To the definition of a monoidal category, we need to add the symmetry component. Catlab calls the swap morphism a braid, because that is how you visualize it in wiring diagrams, but we stick with the conventional σ unicode name. The macro `@op` tells Catlab that you want to use a unicode operator as an alias for you term constructor. If you are familiar with type theory, you might be wondering why we write the context after the terms. This is because human brains are pretty good at type inference based on notational convention and we want to mimic the English idiom "f⋅g, where f:A→B and g:B→C are functions".
# ```julia
# @theory SymmetricMonoidalCategory{Ob,Hom} <: MonoidalCategory{Ob,Hom} begin
#   braid(A::Ob, B::Ob)::((A ⊗ B) → (B ⊗ A))
#   @op (σ) := braid
#   # Involutivity axiom.
#   σ(A,B) ⋅ σ(B,A) == id(A ⊗ B) ⊣ (A::Ob, B::Ob)
#   # Coherence axioms.
#   #
#   # Note: The last two axioms are deducible from the first two axioms together
#   # with the naturality equations for the left/right unitors. We record them for
#   # the sake of clarity and uniformity.
#   σ(A,B⊗C) == (σ(A,B) ⊗ id(C)) ⋅ (id(B) ⊗ σ(A,C)) ⊣ (A::Ob, B::Ob, C::Ob)
#   σ(A⊗B,C) == (id(A) ⊗ σ(B,C)) ⋅ (σ(A,C) ⊗ id(B)) ⊣ (A::Ob, B::Ob, C::Ob)
#   σ(A,munit()) == id(A) ⊣ (A::Ob)
#   σ(munit(),A) == id(A) ⊣ (A::Ob)
#   # Naturality axiom.
#   (f ⊗ g) ⋅ σ(B,D) == σ(A,C) ⋅ (g ⊗ f) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
#                                           f::(A → B), g::(C → D))
# end
# ```

# ## Presentations
# Just like how a preorder can be presented with Hasse Diagram or a free category can be presented by a Graph, SMCs can be presented syntactically or combinatorially. We first start with the syntactic presentation using `@present`.

@present Cooking(FreeSymmetricMonoidalCategory) begin
  (WholeEgg, RawEgg, Shell, Egg, Pan, Cheese, Scramble)::Ob
  crack::Hom(WholeEgg, RawEgg⊗Shell)
  fry::Hom(RawEgg⊗Pan, Egg⊗Pan)
  scramble::Hom(RawEgg⊗Cheese⊗Pan, Scramble⊗Pan)
end

# One interpretation of an SMC is that the objects are resources and the Homs are processes the domain of the Hom is the list of resources that you need to perform the process and the codomain is the list of resources that the process produces. You can think of the SMC presentation as a namespace containing all the terms in the SMC.

# The objects are accessible by name
Cooking[:Egg]

# So are the homs
Cooking[:fry]

# Then you can make complex terms using the unicode operators
((Cooking[:crack]⋅σ(Cooking[:RawEgg], Cooking[:Shell])) ⊗id(Cooking[:Pan])) ⋅ (id(Cooking[:Shell])⊗Cooking[:fry])
# Notice that Catlab will display the expected domain and codomain.

# This is called point-free notation an it is very popular in the functional programming literature where it is used to mean implicit universal quantification over the function arguments. You can think of a morphism like a function that takes an element of each domain object as input and produces an element of each codomain object as output. Not all SMCs have interpretations as functions over sets, but just like groups can be viewed as a generalization of the symmetries of geometric shapes, SMCs can be viewed as a generalization of multivariate functions.

# These presentations are very syntactic objects and expose an API for manipulating expressions.
for g in generators(Cooking)
  "$g is a $(gat_typeof(g)) with arguments $(gat_type_args(g))"
end

# The `gat_typeof` function computes the algebraic type of a term by analogy to `Base.typeof` which computes the Julia type of a value.

homs = filter(generators(Cooking)) do g
  gat_typeof(g) == :Hom
end

# When the term is a Hom, you can get the domain and codomain of the morphism with the `dom` and `codom` functions.
map(homs) do f
  "$f: $(dom(f)) → $(codom(f))"
end

# This syntactic API is useful for manipulating terms in an arbitrary GAT and is the formal language of Catlab for representing and manipulating algebraic structures. 
# However, when we want to work with big expressions in an SMC, the tree structure inherent to formulas is too verbose, and we want to move to a port-graph structure called `DirectedWiringDiagrams`. This gives us the benefits of combinatorial data structures like graphs with the right expressional power for representing the morphisms in an SMC.

recipe = @program Cooking (e::WholeEgg, p::Pan) begin
  e′, shell = crack(e)
  return shell, fry(e′, p)
end
draw(recipe)

# Catlab gives you the tools for drawing wiring diagrams. Visualization of wiring diagrams is the oldest part of Catlab and the original motivation for its development. The `@program` macro allows you to define wiring diagrams using a syntax that feels like Julia code.

# The input wires are declared as *arguments* to the program, and the output wires are declared as *returns* from the function. Variables that are not consumed or by another function or returned by the program are automatically dropped.

recipe = @program Cooking (e::WholeEgg, p::Pan) begin
  e′, shell = crack(e)
  return fry(e′, p)
end
draw(recipe)

# You can copy a value by using it more than once. This is visualized as a wire being split into two wires. Square brackets let you assert equality again. For material goods, you might not want to allow this merging and splitting.
recipe = @program Cooking (e₁::WholeEgg, e₂::WholeEgg, p::Pan) begin
  e, shell = crack(e₁)
  r₁, p₁ = fry(e, p)
  e, shell = crack(e₂)
  r₂, p₂ = fry(e, p)
  return r₁, r₂, [p₁,p₂]
end

draw(recipe)

# You can visualize the copy and delete morphisms explicitly with the `add_junctions` function. The dots with one wire input and multiple outputs are copying values and dots with no wires out are deletions (discarding values). Not all instances of a `SymmetricMonoidalCategory` support copy and delete, for example, in manufacturing you can't duplicate a resource, and in chemistry you can't discard species. Catlab would enforce that when you tried to interpret the wiring diagram in a specific SMC.
draw(add_junctions(recipe))

# For more details about working with wiring diagrams in Catlab, you should look at the vignettes under wiring_diagrams which explain how wiring diagrams interact with SMC expressions and the basics of constructing and manipulation wiring diagrams.

