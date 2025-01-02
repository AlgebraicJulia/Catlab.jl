
# # TODO: The diagrams in a category naturally form a 2-category, but for now we
# # just implement the category structure.

# # Oppositization 2-functor induces isomorphisms of diagram categories:
# #    op(Diag{id}(C)) ≅ Diag{op}(op(C))
# #    op(Diag{op}(C)) ≅ Diag{id}(op(C))

# op(d::Diagram{Any}) = Diagram{Any}(op(diagram(d)))
# op(d::Diagram{id}) = Diagram{op}(op(diagram(d)))
# op(d::Diagram{op}) = Diagram{id}(op(diagram(d)))
# op(f::DiagramHom{id}) = DiagramHom{op}(op(shape_map(f)), op(diagram_map(f)),
#                                        op(f.precomposed_diagram))
# op(f::DiagramHom{op}) = DiagramHom{id}(op(shape_map(f)), op(diagram_map(f)),
#                                        op(f.precomposed_diagram))

# # Any functor ``F: C → D`` induces a functor ``Diag(F): Diag(C) → Diag(D)`` by
# # post-composition and post-whiskering.
# function compose(d::Diagram{T}, F::Functor; kw...) where T
#   Diagram{T}(compose(diagram(d), F; kw...))
# end
# function compose(f::DiagramHom{T}, F::Functor; kw...) where T
#   whiskered = composeH(diagram_map(f), F; kw...)
#   DiagramHom{T}(shape_map(f), whiskered,
#                 compose(f.precomposed_diagram, F; kw...))
# end