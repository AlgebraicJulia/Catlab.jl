# # Visualizing Acset Schemas with Graphviz
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/graphviz_wiring_diagrams.ipynb)
#
# It is convenient to visualize schemas in a non-textual way; often schemas can have many objects, homs and attributes, and it is hard to keep these all in your head.
#
# For this reason, we provide a function which takes a schema and produces a visual representation of it, using the Catlab Graphviz interface.
#
# This is as simple as the following code. These figures are by no means publication-quality, but they can be useful for interactive development.

using Catlab.Present, Catlab.Graphics, Catlab.Graphs

to_graphviz(Graphs.BasicGraphs.TheoryWeightedGraph)
