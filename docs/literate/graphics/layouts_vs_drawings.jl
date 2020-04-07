# # Layouts versus drawings of wiring diagrams
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/layouts_vs_drawings.ipynb)
#
# In Catlab, layout and drawing (rendering) of wiring diagrams are mostly
# decoupled. This notebook shows how to lay out diagrams using Graphviz's
# rank-based layout or Catlab's series-parallel layout and then render them
# using Compose.jl or TikZ.

# The morphism we will visualize is:

using Catlab.Doctrines

X = Ob(FreeSymmetricMonoidalCategory, :X)
f, g, h = (Hom(sym, X, X) for sym in (:f, :g, :h))

expr = otimes(f, compose(f,g), compose(f,g,h))

# Let's convert this expression into a wiring diagram. This yields a purely
# combinatorial object, as evidenced by its underlying graph.

using Catlab.WiringDiagrams, Catlab.Graphics

diagram = to_wiring_diagram(expr)
graph(diagram)

# ## Graphviz layout

# Calling `to_graphviz` both lays out and draws the diagram, entirely within
# Graphviz.

to_graphviz(diagram, orientation=LeftToRight)

# To get just the layout from Graphviz, we call `graphviz_layout` instead. We
# can then render this layout using Compose.jl. Note that the Graphviz layout
# has units in points.

import Compose

layout = graphviz_layout(diagram, orientation=LeftToRight)
layout_to_composejl(layout, base_unit=Compose.pt)

# The same layout can be rendered in TikZ:

import TikzPictures

layout_to_tikz(layout, base_unit="1pt")

# ## Series-parallel layout

# Catlab has its own layout system based on series-parallel decomposition. In
# this case, the layout exactly recovers the structure of the morphism
# expression created at the beginning.

layout = layout_diagram(FreeSymmetricMonoidalCategory, diagram,
                        orientation=LeftToRight)
layout_to_composejl(layout)
#-
layout_to_tikz(layout)
