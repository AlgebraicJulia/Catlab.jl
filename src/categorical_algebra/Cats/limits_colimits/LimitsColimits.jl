export image, coimage, epi_mono, bundle_legs, DefaultAlg, factorize, universal

using StructEquality
using StaticArrays: SVector

using GATlab

using ....Theories: universal
using ..FreeDiagrams
using ..Categories: Category
import ..Categories: obtype, homtype

# """
# Extend the theory of categories with some extra datatypes (with intended 
# associated Julia types) useful in both limits and colimits
# """
# @theory ThCategoryDiag <: ThCategory begin
#   # Diagram types
#   Disc::TYPE; Span′::TYPE; Cospan′::TYPE; Par::TYPE; BPFD::TYPE; FD::TYPE;
#   Lim::TYPE; Alg::TYPE;
#   BareHom::TYPE; # when we have a hom but don't know its dom/codom statically
# end


# """
# Implement this for each diagram impl + category combination.

# `_universal` expects the following arguments: 
# - the diagram impl 
# - the category the diagram is in 
# - the (co)cone result of the (co)Limit
# - the multi(co)span to which we are applying the universal property
# """
# function _universal end 


# Algorithms
############

""" A limit *or* a colimit algorithm """
abstract type LimitAlgorithm end





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
bundle_legs(span::Multispan, indices, m) =
  Multispan(apex(span), map(i -> bundle_leg(span, i, m), indices))
  
bundle_legs(cospan::Multicospan, indices, m) =
  Multicospan(apex(cospan), map(i -> bundle_leg(cospan, i, m), indices))

bundle_leg(x::Union{Multispan,Multicospan}, i::Int, ::Any) = legs(x)[i]

bundle_leg(x::Union{Multispan,Multicospan}, i::Tuple, m
           ) = bundle_leg(x, SVector(i), m)

bundle_leg(span::Multispan, i::AbstractVector{Int}, m
          ) = pair[m](legs(span)[i]...)

