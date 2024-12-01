module LimitsColimits  
export image, coimage, epi_mono, bundle_legs, DefaultAlg, factorize, universal

using Reexport
using StructEquality
using StaticArrays: SVector

import GATlab: getvalue

using ....Theories: universal
using ..FreeDiagrams
import ..FreeDiagrams: getcategory, ob, apex, legs
import ..FinFunctors: diagram
using ..Categories: Category
import ..Categories: obtype, homtype


# Data structures for (co)limits
################################

# Abstract types
#---------------

abstract type LimColim end # for shared code between limits and colimits

getvalue(l::LimColim) = l.impl

diagram(l::LimColim) = l.diag

getcategory(l::LimColim) = getcategory(diagram(l))

obtype(l::LimColim) = obtype(getcategory(l))

homtype(l::LimColim) = homtype(getcategory(l))

ob(colim::LimColim) = apex(colim)

""" Implemented in Limits.jl and Colimits.jl """
function cone_cocone end 

apex(lim::LimColim) = apex(cone_cocone(lim)) 

legs(lim::LimColim) = legs(cone_cocone(lim))

Base.iterate(lim::LimColim, x...) = iterate(cone_cocone(lim), x...)

Base.length(lim::LimColim) = length(cone_cocone(lim))


"""
Implement this for each diagram impl + category combination.

`_universal` expects the following arguments: 
- the diagram impl 
- the category the diagram is in 
- the (co)cone result of the (co)Limit
- the multi(co)span to which we are applying the universal property
"""
function _universal end 


# Algorithms
############

""" A limit *or* a colimit algorithm """
abstract type LimitAlgorithm end

""" Default algorithm for (co)limits """
@struct_hash_equal struct DefaultAlg <: LimitAlgorithm end 


# Limits and colimits
#####################
include("Limits.jl")
include("Colimits.jl")

@reexport using .Limits 
@reexport using .Colimits

# Named (co)limits
##################

"""https://en.wikipedia.org/wiki/Image_(category_theory)#Second_definition"""
image(f, m::Category) = equalizer(legs(pushout(f,f, m))...)

"""https://en.wikipedia.org/wiki/Coimage"""
coimage(f, m::Category) = coequalizer(legs(pullback(f, f, m))...)


"""
The image and coimage are isomorphic. We get this isomorphism using univeral
properties.

      CoIm′ ╌╌> I ↠ CoIm
        ┆ ⌟     |
        v       v
        I   ⟶  R ↩ Im
        |       ┆
        v    ⌜  v
        R ╌╌> Im′
"""
function epi_mono(f, m::Category)
  Im, CoIm = image(f, m), coimage(f, m)
  iso = factorize(Im, factorize(CoIm, f))
  ComposablePair(proj(CoIm) ⋅ iso, incl(Im))
end



# Bundling
###########

""" Bundle together legs of a multi(co)span.

For example, calling `bundle_legs(span, SVector((1,2),(3,4)))` on a multispan
with four legs gives a span whose left leg bundles legs 1 and 2 and whose right
leg bundles legs 3 and 4. Note that in addition to bundling, this function can
also permute legs and discard them.

The bundling is performed using the universal property of (co)products, which
assumes that these (co)limits exist.
"""
bundle_legs(span::Multispan, indices, m::Category) =
  Multispan(apex(span), map(i -> bundle_leg(span, i, m), indices))
  
bundle_legs(cospan::Multicospan, indices, m::Category) =
  Multicospan(apex(cospan), map(i -> bundle_leg(cospan, i, m), indices))

bundle_leg(x::Union{Multispan,Multicospan}, i::Int, ::Category) = legs(x)[i]

bundle_leg(x::Union{Multispan,Multicospan}, i::Tuple, m::Category
           ) = bundle_leg(x, SVector(i), m)

bundle_leg(span::Multispan, i::AbstractVector{Int}, m::Category
          ) = pair(legs(span)[i], m)

bundle_leg(cospan::Multicospan, i::AbstractVector{Int}, m::Category  
          )  = copair(legs(cospan)[i], m)

end # module
