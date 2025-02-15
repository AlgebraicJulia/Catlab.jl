module FreeDiagramFunctors
export FreeDiagramFunctor

using GATlab 
using .....BasicSets, ...Cats, ..FinFunctors

""" View a FinDomFunctor as a FreeDiagram """
struct FreeDiagramFunctor{DO,DG,CO,CH}
  val::FinDomFunctor 
end 

GATlab.getvalue(f::FreeDiagramFunctor) = f.val

@instance ThFreeDiagram{V=DO,E=DG,Ob=CO,Hom=CH} [model::FreeDiagramFunctor{DO,DG,CO,CH}
                                ] where {DO,DG,CO,CH} begin
  src(i::DG)::DO = dom(dom(getvalue(model)), i) 
  tgt(i::DG)::DO = codom(dom(getvalue(model)), i) 
  obmap(i::DO)::CO = ob_map(getvalue(model), i)
  hommap(i::DG)::CH = hom_map(getvalue(model), i)
  obset()::FinSet = ob_set(dom(getvalue(model)))
  homset()::FinSet = hom_set(dom(getvalue(model)))
end

end # module