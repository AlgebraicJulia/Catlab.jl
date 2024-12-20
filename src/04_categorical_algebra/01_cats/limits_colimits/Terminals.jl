module Terminals 
export TerminalLimit, ThCategoryWithTerminal, CatWithTerminal, delete, terminal

using StructEquality

using GATlab
using GATlab.Syntax.TheoryInterface: WithModel

import .....Theories: terminal, delete, ◊, universal, ob
using ...Categories: Category
using ...FreeDiagrams
using ..Limits: AbsLimit, DefaultLimit
import ..Limits: limit, cone

"""
`Terminal` is expected to be implemented by `TerminalLimit`.
"""
@theory ThCategoryWithTerminal <: ThCategory begin
  Terminal()::TYPE
  terminal()::Terminal()
  ob(⊤::Terminal())::Ob
  universal(⊤::Terminal(), C::Ob)::(C → ob(⊤))
  ◊(C::Ob)::(C → ob(terminal())) # := universal(terminal(), C) TODO implement AlgFun
end

# hack this into every model (still need to @import it)
◊(m::WithModel, x; context) = delete(m, terminal(m; context), x; context)

delete(C, x) = universal(C, terminal(C), x)


""" Any implementation of a TerminalLimit is just an object """
@struct_hash_equal struct TerminalLimit{Ob,Hom} <: AbsLimit 
  ob::Ob
end

cone(s::TerminalLimit{Ob,Hom}) where {Ob, Hom} = Multispan(s.ob, Hom[])

ThCategoryWithTerminal.Meta.@wrapper CatWithTerminal

limit(c::CatWithTerminal, ::EmptyDiagram) = terminal(c)

terminal(m::Category; alg=DefaultLimit()) = limit(Diagram(m); alg)

end # module
