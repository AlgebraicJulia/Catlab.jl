# # Decorated Cospans of Dynamical Systems

using Catlab
import Catlab.Theories: compose, id, dom, codom
using Catlab.CategoricalAlgebra
import Catlab.CategoricalAlgebra.Limits: CompositePushout
using Catlab.Decorated
using Catlab.Sheaves
import Catlab.CategoricalAlgebra.Categories: do_ob_map, do_hom_map, LargeCatSize

# ## Defining our Functor
#
# Decorated Cospans requires that you map objects of FinSet (Natural Numbers) to 
# Sets of systems with that size. In this case our systems of size $n$ are vector fields on $\mathbb{R}^n$.
# The systems need to be able to act on a vector in their state space to produce a tangent vector.
struct DynamElt
  n::Int
  v::Function # ℝⁿ→Tℝⁿ
end

(v::DynamElt)(x::AbstractVector) = v.v(x)

# A DynamMap is a wrapper around a FinFunction to hang our functor's action on.

struct DynamMap
  f::FinFunction 
end

dom(f::DynamMap) = dom(f.f)
codom(f::DynamMap) = codom(f.f)

# A `DynamMap` acts of a `DynamElt` $v$ by computing a new `DynamElt` $u$ 
# that is derived by a change of variables.
# You first pullback the state of $u$ to a state of $v$ by precomposition by $f$.
# Then you apply the vector field $v$ by calling the function to get a tangent vector $v(f^*(x))$.
# Then you pushforward the tangent vector by adding up variables that get mapped to the same state variable by $f$.

(f::DynamMap)(v::DynamElt) = begin
  FinSet(v.n) == dom(f) || error("Domain of finfunction must match state space of dynamical system")
  pushforward = do_hom_map(FVectPushforward, f.f)
  pullback    = do_hom_map(FVectPullback(),    f.f)
  DynamElt(dom(f).n, pushforward∘v.v∘pullback)
end

# Our category of dynamical systems is a subcategory of Set.
# Each `Int` represents the set of vector fields on $n$ variables and 
# each `DynamMap` represents a function from vector fields on $n$ variables to vector fields on $m$ variables.

struct DynamCat <: Category{Int, DynamMap, LargeCatSize} end

F = Functor(identity, f -> DynamMap(f), FinSetCat(), DynamCat())

# We can test out our dynamics functor on some basic equations.
# These are using the identity function x->x as the starting vector field.
# This allows us to write tests that are easy to reason about.

using Test
f = FinFunction([2,1], 2)
ϕ = do_hom_map(F, f)
@test dom(ϕ) == FinSet(2)

v = x->[x[1],x[2]]
u = ϕ(DynamElt(2, v))
@test u([π,exp(1)]) == [π, exp(1)]

g = FinFunction([2,1,2], 2)
ψ = do_hom_map(F, g)
w = identity
u = ψ(DynamElt(3, w))
@test u([π,exp(1)]) == [π, 2exp(1)]

f = FinFunction([2,1,2,1], 2)
ϕ = do_hom_map(F, f)
v = identity
u = ϕ(DynamElt(4, v))
@test u([π,exp(1)]) == [2π, 2exp(1)]

f = FinFunction([2,1,2,1], 3)
ϕ = do_hom_map(F, f)
v = identity
u = ϕ(DynamElt(4, v))
@test u([π,exp(1),1]) == [2π, 2exp(1), 0]

# We can use a polynomial vector field for some interesting computations. 
# Notice that you can quickly build some complex vector fields with the action of
# FinFunctions on polynomial primitives.

f = FinFunction([2,1,2,1], 3)
ϕ = do_hom_map(F, f)
v = x->[x[1]*x[2], x[2], x[3]*x[1], x[4]]
u = ϕ(DynamElt(4, v))
@test u([π,exp(1),1]) == [2π, exp(1)*π + exp(1)^2, 0]

# Now let's do some decorated cospans in Dynam. We start by defining our laxator $L$.

# ## Defining the Laxator
# 
# The Laxator is usually easier than the functor. 
# In this case we just have to implement stacking vector fields on top of each other.
# This is the categorical product of functions in set.
# If you have functions $f\colon \mathbb{R}^n\to T\mathbb{R}^n$ and $f\colon \mathbb{R}^m\to T\mathbb{R}^m$,
# the categorical product is a function $f\times g \colon \mathbb{R}^{n+m}\to T\mathbb{R}^{n+m}$.
# You just call $f$ on the first $n$ variables and $g$ on the $n+1:n+m$ variables and concatenate their output.
# In Vect (the cateogry of vector spaces and linear maps), this categorical product is also the coproduct, and we call it the direct sum ($\oitmes$).

L(vs::Vector{DynamElt}) = begin
  @show vs
  indices = cumsum(v.n for v in vs)
  pushfirst!(indices, 0)
  @show indices
  f(x) = begin
    dx = map(enumerate((vs))) do (i,v)
      xᵢ = x[indices[i]+1:indices[i+1]]
      dxᵢ = v(xᵢ)
    end
    reduce(vcat, dx)
  end
  return DynamElt(indices[end], f)
end


# And we can test that our Laxator is working

w = L([DynamElt(2, identity),DynamElt(3, identity)])
@test w(1:5) == 1:5

w = L([DynamElt(2, x->[x[1]*x[2],x[2]]),DynamElt(3, x->[x[1]*x[2], x[2], x[3]])])
@test w(1:5) == [2*1, 2, 3*4, 4,5]

# ## Decorated Cospans of Dynam
# Now that our Functor and Laxator are working, we can move on to the Decorated Cospans.
# Note that we call the lax monoidal functor the "decora*tor*" and the
# systems that we use to decorate our cospans the "decora*tions*".
# The decorations are elements in the image of the decorator.

# Here we are gluing the second and third variables of $v$ to the first and second variables of $u$.

D = Decorated.Decorator(F, L)
f = FinFunction([2,3], 3)
g = FinFunction([1,2], 3)
v = DynamElt(3, identity)
u = DynamElt(3, identity)
w = glue(D, pushout(f,g), [v,u])
@test w([1,2,3,5]) == [1,4,6,5]

# With interesting vector fields we can get cool dynamics.

v = DynamElt(3, x->[x[1]*x[2], x[2], x[3]])
u = DynamElt(3, x->[x[1], x[2]*x[3], x[3]])
w = glue(D, pushout(f,g), [v,u])
@test w([1,2,3,4]) == [1*2,2,3,0] + [0,2,3*4,4]
@test w([2,3,5,7]) == [2*3,3,5,0] + [0,3,5*7,7]

# ## Euler's Method

# Can apply Euler's method to produce trajectories of these systems.

v = DynamElt(3, x->[x[1]*x[2], x[2], -x[3]])
u = DynamElt(3, x->[x[1], x[2]*x[3]/x[1], x[3]])
w = glue(D, pushout(f,g), [v,u])
x = Vector{Float64}[[2,3,5,7]]
Δt = 0.05
map(1:10) do i
  xᵢ₊₁ = x[i] + w(x[i])*Δt
  push!(x, xᵢ₊₁)
end
traj = hcat(x...)';

# We can look at our trajectory as a table.

using PrettyTables
pretty_table(traj)

# ## Implementing Corelations for Dynamical Systems
# Can we define a restriction map on dynamical systems that is given by "solving for equilibrium on the hidden variables"?

using NLsolve
abstract type EquilibriumProjection <: Functor{FinSetCat, DynamCat} end

range_complement(m::FinFunction) = sort(setdiff(collect(codom(m)), unique(m.(dom(m)))))
pullback_complement(m::FinFunction) = do_hom_map(FMatPullback(), FinFunction(range_complement(m), codom(m)))

range_complement(FinFunction([1,3], 4))
@test range_complement(FinFunction([1,3], 4)) == [2,4]

# Assuming that f is a mono from Y to X
# s:S = X\Y
# pushforward = do_hom_map(FVectPushforward, f)
# pullback    = pushforward'
EquilibriumProjection(f::FinFunction) = begin
  π₁ = do_hom_map(FMatPullback(), f)
  i₁ = π₁'
  π₂ = pullback_complement(f)
  i₂ = π₂'
  st(s,y) = begin
    a = i₁*y
    b = i₂*s
    c = a+b
    return c
  end

  (v::DynamElt) -> begin
    u(y) = begin
      s̄ = nlsolve(s->π₂*v(st(s,y)),zeros(size(i₂,2))).zero
      @show s̄
      π₁*v(st(s̄, y))
    end
    DynamElt(dom(f).n, u)
  end
end

f = FinFunction([1,2], 3)
u = DynamElt(3, x->[-x[1]*x[3],-x[2]/2, -(x[3]-1/2)*0.999999])
v = EquilibriumProjection(f)(u)

x = Vector{Float64}[[1,1]]
Δt = 0.05
map(1:20) do i
  xᵢ₊₁ = x[i] + v(x[i])*Δt
  push!(x, xᵢ₊₁)
end
traj = hcat(x...)';
pretty_table(traj)