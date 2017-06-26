""" Finite presentations of a model of a generalized algebraic theory (GAT).

We support two methods for defining models of a GAT: as Julia objects using the
`@instance` macro and as syntactic objects using the `@presentation` macro.
Instances are useful for casting generic data structures, such as matrices,
abstract tensor systems, and wiring diagrams, in categorical language.
Presentations define small categories by a set generators and relations and are
useful for applications like knowledge representation.
"""
module Presentation
export @presents

using Match

# Data types
############

# Presentations
###############

macro presents(head, body)
  
end

end
