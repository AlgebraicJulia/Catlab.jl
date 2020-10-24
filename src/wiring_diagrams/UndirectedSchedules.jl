module UndirectedWiringDiagramSchedules
export AbstractUWDSchedule, UWDSchedule

using ..Undirected: TheoryUWD

# Data types
############

@present TheoryUWDSchedule <: TheoryUWD begin
  Composite::Ob

  box_in::Hom(Box, Composite)
  junction_in::Hom(Box, Composite)
  parent_composite::Hom(Composite, Composite)
  parent_junction::Hom(Junction, Junction)

  # Outer junctions belong to root-level composites.
  compose(outer_junction, junction_in, parent_composite) ==
    compose(outer_junction, junction_in)

  # Po-category axioms: for now, just comments.
  # Rooted forest of composites and rooted forest of junctions.
  #parent_composite <= id(Composite)
  #parent_junction <= id(Junction)

  # Intertwining of junction and composite forests.
  #compose(parent_junction, junction_in) >=
  #  compose(junction_in, parent_composite)
  #compose(parent_junction, junction_in) <= junction_in
end

end
