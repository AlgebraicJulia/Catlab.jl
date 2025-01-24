module MonoidalLimits 
export @cartesian_monoidal_instance

using GATlab

using .....Theories

""" Define cartesian monoidal structure using limits.

Implements an instance of [`ThCartesianCategory`](@ref) assuming that finite
products have been implemented following the limits interface.
"""
macro cartesian_monoidal_instance(Ob, Hom)
  thcc = ThCartesianCategory.Meta.theory
  instance_body = quote
    @import Ob, Hom, →, dom, codom, compose, ⋅, id, munit, delete, pair

    otimes(A::$Ob, B::$Ob) = ob(product(A, B))

    function otimes(f::$Hom, g::$Hom)
      π1, π2 = product(dom(f), dom(g))
      pair(product(codom(f), codom(g)), π1⋅f, π2⋅g)
    end

    function braid(A::$Ob, B::$Ob)
      AB, BA = product(A, B), product(B, A)
      pair(BA, proj2(AB), proj1(AB))
    end

    mcopy(A::$Ob) = pair(id(A),id(A))
    proj1(A::$Ob, B::$Ob) = proj1(product(A, B))
    proj2(A::$Ob, B::$Ob) = proj2(product(A, B))
  end

  instance_code = ModelInterface.generate_instance(
    ThCartesianCategory.Meta.theory,
    ThCartesianCategory,
    Dict(zip(sorts(thcc), [Ob, Hom])),
    nothing,
    [],
    instance_body;
    escape=false
  )

  esc(quote
    import Catlab.Theories: ThCartesianCategory, otimes, ⊗, munit, braid, σ,
      mcopy, delete, pair, proj1, proj2, Δ, ◊

    $instance_code

    otimes(As::AbstractVector{<:$Ob}) = ob(product(As))

    function otimes(fs::AbstractVector{<:$Hom})
      Π, Π′ = product(map(dom, fs)), product(map(codom, fs))
      pair(Π′, map(compose, legs(Π), fs))
    end

    munit(::Type{T}) where T <: $Ob = ob(terminal(T))
  end)
end

end # module
