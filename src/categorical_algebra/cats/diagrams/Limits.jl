
import ..LimitsColimits: limit, colimit, universal

# In a cocomplete category `C`, colimits define a functor `Diag{id,C} → C`.
# Dually, in a complete category `C`, limits define functor `Diag{op,C} → C`.

limit(d::FinDomFunctor; alg=nothing) = limit(diagram(d), alg)

colimit(d::FinDomFunctor; alg=nothing) = colimit(diagram(d), alg)

function universal(::WithModel{DiagramOp}, f::DiagramHom, dom_lim, codom_lim)
  J′ = shape(codom(f))
  obs = Dict(reverse(p) for p in pairs(ob_generators(dom(diagram(dom(f))))))
  cone = Multispan(apex(dom_lim), map(ob_generators(J′)) do j′
    j, g = ob_map(f, j′)
    πⱼ = legs(dom_lim)[obs[j]]
    compose(πⱼ, g)
  end)
  universal(codom_lim, cone)
end

function universal(::WithModel{Diagram},f::DiagramHom, dom_colim, codom_colim)
  J = shape(dom(f))
  obs = Dict(reverse(p) for p in pairs(ob_generators(dom(diagram(codom(f))))))
  cocone = Multicospan(apex(codom_colim), map(ob_generators(J)) do j
    j′, g = ob_map(f, j)
    ιⱼ′ = legs(codom_colim)[obs[j′]]
    compose(g, ιⱼ′)
  end)
  universal(dom_colim, cocone)
end
