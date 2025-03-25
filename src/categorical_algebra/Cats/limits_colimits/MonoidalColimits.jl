module MonoidalColimits 
export @cocartesian_monoidal_instance

using GATlab

using .....Theories

""" Define cocartesian monoidal structure using colimits.

Implements an instance of [`ThCocartesianCategory`](@ref) assuming that finite
coproducts have been implemented following the colimits interface.
"""
macro cocartesian_monoidal_instance(Ob, Hom)
  esc(quote
    import Catlab.Theories: ThCocartesianCategory, oplus, ⊕, mzero, swap,
      plus, zero, copair, coproj1, coproj2

    @instance ThCocartesianCategory{$Ob, $Hom} begin
      @import dom, codom, compose, ⋅, id, mzero, copair

      oplus(A::$Ob, B::$Ob) = ob(coproduct(A, B))

      function oplus(f::$Hom, g::$Hom)
        ι1, ι2 = coproduct(codom(f), codom(g))
        copair(coproduct(dom(f), dom(g)), f⋅ι1, g⋅ι2)
      end

      function swap(A::$Ob, B::$Ob)
        AB, BA = coproduct(A, B), coproduct(B, A)
        copair(AB, coproj2(BA), coproj1(BA))
      end

      plus(A::$Ob) = copair(id(A),id(A))
      zero(A::$Ob) = create(A)
      coproj1(A::$Ob, B::$Ob) = coproj1(coproduct(A, B))
      coproj2(A::$Ob, B::$Ob) = coproj2(coproduct(A, B))
    end

    oplus(As::AbstractVector{<:$Ob}) = ob(coproduct(As))

    function oplus(fs::AbstractVector{<:$Hom})
      ⊔, ⊔′ = coproduct(map(dom, fs)), coproduct(map(codom, fs))
      copair(⊔, map(compose, fs, legs(⊔′)))
    end

    mzero(::Type{T}) where T <: $Ob = ob(initial(T))
  end)
end


end # module
