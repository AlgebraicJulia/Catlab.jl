# # Diagrams
# Catlab supports the expression of equations in an arbitrary category via diagrams, or functors from a finitely presented category. This view of diagrammatic equations builds on the Catlab approach to functorial semantics by asserting that a system of equations of shape J is a functor F: J → 𝐂. We can draw these equations with Graphviz, where each node is an object in X:Ob(J) labeled with its type F(X) and each edge is a morphism in J labeled with its image under F. 
using Catlab
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FreeDiagrams
using Catlab.CategoricalAlgebra.Diagrams
using Catlab.Programs.DiagrammaticPrograms
using Catlab.Graphs
using Catlab.Graphs.BasicGraphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Catlab.Theories
using Catlab.Syntax
using Catlab.Graphics.FinFunctors

draw(D::FinFunctor) = to_graphviz(D, node_labels=true, edge_labels=true, prog="neato")

# ## Present a diagram in a given category.
# Recall that a *diagram* in a category ``C`` is a functor ``F: J → C`` from a
# small category ``J`` into ``C``. Given the category ``C``, this macro presents a
# diagram in ``C``, i.e., constructs a finitely presented indexing category ``J``
# together with a functor ``F: J → C``. This method of simultaneous definition is
# often more convenient than defining ``J`` and ``F`` separately.
# often more convenient than defining ``J`` and ``F`` separately, as could be
# accomplished by calling [`@fincat`](@ref) and then [`@finfunctor`](@ref).
# For example, the limit of the following diagram consists of the paths of length
# two in a graph:

D₂ = @free_diagram BasicGraphs.TheoryGraph begin
    v::V
    (e₁, e₂)::E
    tgt(e₁) == v
    src(e₂) == v
end

# Morphisms in the indexing category can be left unnamed, which is convenient for defining free diagrams (see also [`@free_diagram`](@ref)). Of course, unnamed morphisms cannot be referenced by name within the `@diagram` call or in other settings, which can sometimes be problematic.
# 
# ## Presenting a free diagram in a given category.
# Recall that a *free diagram* in a category ``C`` is a functor ``F: J → C`` where ``J`` is a free category on a graph, here assumed finite. This macro is functionally a special case of [`@diagram`](@ref) that provides a syntactic variant for equality expressions. Rather than interpreting them as equations between morphisms in ``J``, equality expresions can be used to introduce anonymous morphisms in a "pointful" style. For example, the limit of the following diagram consists of the paths of length two in a graph:
    
draw(D₂)

# For small equations the point-free notation commonly employed in functional programming is very convenient; however, there is a reason it is not the standard approach to presenting equations in mathematical writing. Variables are just too useful! As the size of the system of equations grows, it becomes more and more convenient to use variable names. This is why `Catlab.Programs.@program` exists to help people write SMC morphisms with the point-ful notation they are familiar with in imperative or procedural programming.

# We can describe a triangle in a graph using the vertex variables v₁, v₂, v₃ and edge variables e₁, e₂, e₃. Then we use the equation notation to assert the `src` and `tgt` relationships between the edges and vertices. 
D₃ = @free_diagram BasicGraphs.TheoryGraph begin
    (v₁, v₂, v₃)::V
    (e₁, e₂, e₃)::E
    src(e₁) == v₁
    tgt(e₁) == v₂
    src(e₂) == v₂
    src(e₃) == v₁
    tgt(e₂) == v₃
    tgt(e₃) == v₃
end

# You can see the shape of a triangle when you draw this diagram. This coincidence can be systematically understood (by an experienced category theorist) via the Grothendieck construction and representable functors. 
draw(D₃)

# ## Sequences in 𝐂
# In any category with an endomorphism f: A → A, we can think of recurrence equations as aₙ = f(fⁿ⁻¹(a₀))
@present 𝗖(FreeCartesianCategory) begin
    (A,B)::Ob
    f::Hom(A,A)
    g::Hom(A,B)
end

seq₃ = @free_diagram 𝗖 begin
    (a₀,a₁,a₂,a₃)::A
    a₁ == f(a₀)
    a₂ == f(a₁)
    a₃ == f(a₂)
end

draw(seq₃)

# Inspired by linear recurrence relations like the Fibonacci sequence we can think of A and B as vector spaces. An endomorphism f: A → A and morphism g: A → B defines a linear recurrence by applying f to update the system state and g to compute the current term in the sequence. This can be visualized as follows.


obs_seq₃ = @free_diagram 𝗖 begin
(a₀,a₁,a₂,a₃)::A
(b₁, b₂, b₃ )::B
a₁ == f(a₀)
b₁ == g(a₁)
a₂ == f(a₁)
b₂ == g(a₂)
a₃ == f(a₂)
b₃ == g(a₃)
end
draw(obs_seq₃)

# In the case of the Fibonacci sequence A is ℝ² and B is ℝ with f = [1 1; 1 0] and g = π₁.

@present 𝐃(FreeCartesianCategory) begin
    (ℝ²,ℝ)::Ob
    f::Hom(ℝ²,ℝ²)
    π₁::Hom(ℝ²,ℝ)
end

fib_seq₃ = @free_diagram 𝐃 begin
    (a₀,a₁,a₂,a₃)::ℝ²
    (b₁, b₂, b₃ )::ℝ
    a₁ == f(a₀)
    b₁ == π₁(a₁)
    a₂ == f(a₁)
    b₂ == π₁(a₂)
    a₃ == f(a₂)
    b₃ == π₁(a₃)
end

draw(fib_seq₃)

# ## Newton's Method
# The equations that we have seen aren't particularly interesting, so we turn to a classic of numerical methods. Newton's method for root finding. For an overview of Netwon's method see [Fundamentals of Numerical Computation](https://fncbook.github.io/fnc/nonlineqn/newton.html). The following presentation doesn't know that f′ is the derivative of f, they are just two functions that are evocatively named. We could use [CombinatorialSpaces.jl](https://github.com/AlgebraicJulia/CombinatorialSpaces.jl) to formulate this in a richer categorical setting where we could assert `f := f`. 
@present Analytic(FreeCartesianCategory) begin
    (ℝ,ℝ²)::Ob
    π₁::Hom(ℝ², ℝ)
    π₂::Hom(ℝ², ℝ)
    plus ::Hom(ℝ², ℝ)
    times::Hom(ℝ², ℝ)
    f    ::Hom(ℝ,ℝ)
    f′   ::Hom(ℝ,ℝ)
end
# According to the standard formula xₖ₊₁ = xₖ - f(xₖ)/f′(xₖ). The standard presentation of Newton's method relies on the fact that ℝ is a field to use division in the definition of the iterative procedure. Because of the constraint that you can't divide by 0 in a field, fields are not models of any algebraic theory. Because of this, we can multiply both sides by f′(xₖ) and define a Newton's method iteration without reference to division. We also can avoid negation by adding the f(xₖ) term on both sides.
newtons = @free_diagram Analytic begin
    # times(f′(xₖ₊₁), xₖ₊₁) == times(f′(xₖ₊₁), x) - f(xₖ)
    # plus(times(f′(xₖ₊₁), xₖ₊₁), f(xₖ)) == times(f′(xₖ₊₁), x)
    (xₖ, xₖ₊₁, dₖ, fx, ∏, Σ)::ℝ
    (p₁, p₂, p₃)::ℝ²
    dₖ  == f′(xₖ)
    π₁(p₁) == dₖ
    π₂(p₁) == xₖ₊₁
    ∏ == times(p₁)
    fx == f(xₖ)
    π₁(p₂) == ∏ 
    π₂(p₂) == fx 
    plus(p₂) == Σ
    π₁(p₃) == dₖ
    π₂(p₃) == xₖ
    times(p₃) == Σ
end

draw(newtons)

# This is definitely a case where standard mathematical notation wins for brevity and clarity. We need a few ergonamic improvements to the diagrammatic equation approach in order to compete with tradtitional notation.
# 1. The ability to assert equations without introducing temporary variables,
# 2. The ability to represent morphisms f: A×B → C as bivariate functions like `f(a:A, b:B)`,
# While encoding simple equations can be more verbose than the traditional notation, the diagrammatic encoding provides a direct route to creating a category whose objects are systems of equations and whose morphisms are relationships between systems of equations. That category is the first step towards leveraging the constructive approach in Catlab to making hierarchical representations of complex systems of equations.
