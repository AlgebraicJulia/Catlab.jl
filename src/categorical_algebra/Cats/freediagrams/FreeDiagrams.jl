export FixedShapeFreeDiagram,
  diagram_type, cone_objects, cocone_objects, cocone_indices,
  ob, hom, dom, codom

using GATlab
import AlgebraicInterfaces: ob, hom, dom, codom

# Diagram interface
###################

""" Given a diagram in a category ``C``, return Julia type of objects and
morphisms in ``C`` as a tuple type of form ``Tuple{Ob,Hom}``.
"""
function diagram_type end

""" Objects in diagram that will have explicit legs in limit cone.

In category theory, it is common practice to elide legs of limit cones that can
be computed from other legs, especially for diagrams of certain fixed shapes.
For example, when it taking a pullback (the limit of a cospan), the limit object
is often treated as having two projections, rather than three. This function
encodes such conventions by listing the objects in the diagram that will have
corresponding legs in the limit object created by Catlab.

See also: [`cocone_objects`](@ref).
"""
cone_objects(diagram) = ob(diagram)

""" Objects in diagram that will have explicit legs in colimit cocone.

See also: [`cone_objects`](@ref).
"""
cocone_objects(diagram) = ob(diagram)

# Diagrams of fixed shape
#########################

""" Abstract type for free diagram of fixed shape.
"""
abstract type FixedShapeFreeDiagram{Ob,Hom} end

diagram_type(::FixedShapeFreeDiagram{Ob,Hom}) where {Ob,Hom} = Tuple{Ob,Hom}

