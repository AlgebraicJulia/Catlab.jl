
export co, Cat2, component, dom_ob, codom_ob, is_natural

using StructEquality
using Reexport

using GATlab
import GATlab: getvalue

using ....Theories: ThCategory2
import .ThCategory2: dom, codom, compose, ⋅, ∘, id, composeH, *
using ..Categories: Cat
using ..Functors: Functor

# Natural transformations
#########################

# The equations that come with this will be less tedious to do when colimits 
# of GATs are a thing
@theory ThTransformation begin
  DO::TYPE; CH::TYPE; Fun::TYPE
  dom()::Fun 
  codom()::Fun
  component(x::DO)::CH
end

ThTransformation.Meta.@wrapper Transformation 

function validate(i::Transformation)
  F, G = ThTransformation.dom[i](), ThTransformation.codom[i]()
  dom(F) == dom(G) || error("Domains don't match")
  codom(F) == codom(G) || error("Codomains don't match")
  obtype(dom(F)) == DO || error("Bad dom ob type")
  homtype(codom(F)) == CH || error("Bad codom hom type")
  new{DO,CH}(i)
end


@inline Base.getindex(α::Transformation, c) = component(α, c)

""" Domain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``C``.
"""
dom_ob(α::Transformation) = dom(dom(α)) # == dom(codom(α))

""" Codomain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``D``.
"""
codom_ob(α::Transformation) = codom(dom(α)) # == codom(codom(α))

