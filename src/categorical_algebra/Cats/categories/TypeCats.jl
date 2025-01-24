module TypeCats 
export TypeCat

using ..Categories
import ..Categories: ob, hom

""" Pair of Julia types regarded as a category.

The Julia types should form an `@instance` of the theory of categories
(`Theories.Category`).
"""
struct TypeCat{Ob,Hom} <: Cat{Ob,Hom,LargeCatSize} end

TypeCat(Ob::Type, Hom::Type) = TypeCat{Ob,Hom}()

# FIXME: Type conversion isn't practical because types are often too tight.
#ob(::TypeCat{Ob,Hom}, x) where {Ob,Hom} = convert(Ob, x)
#hom(::TypeCat{Ob,Hom}, f) where {Ob,Hom} = convert(Hom, f)
ob(::TypeCat, x) = x
hom(::TypeCat, f) = f

Base.show(io::IO, ::TypeCat{Ob,Hom}) where {Ob,Hom} =
  print(io, "TypeCat($Ob, $Hom)")

end # module
