module DPO
export rewrite, match_pat

import ...Graphs.BasicGraphs: Graph, nv, edges, add_edges!, neighbors,has_edge, src, tgt
using ..FinSets
import ..CSets: ACSetTransformation, CSetTransformation, components, homomorphism, homomorphisms, unpack_components, pack_components
using ...Theories
using ..Limits
using ..FinSets
using ...Graphs.BasicGraphs


"""Edge ids in codomain not in image of a morphism."""
function orphan_edges(l::CSetTransformation)::Set{Int}
    image = Set(l.components[:E].func)
    return setdiff(Set(1:length(l.codom.tables[:E])), image)
end

"""Node ids in codomain not in image of a morphism."""
function orphan_nodes(l::CSetTransformation)::Set{Int}
    image = Set(l.components[:V].func)
    return setdiff(Set(1:length(l.codom.tables[:V])), image)
end

function rem_node_codomain(f::CSetTransformation, n::Int)::CSetTransformation
    new_dom = deepcopy(f.dom)
    new_codom = deepcopy(f.codom)
    rem_vertex!(new_codom, n)

    oldV = f.components[:V]
    newFunc = Int[]
    for x in oldV.func
        if x < n
            push!(newFunc, x)
        elseif x > n
            push!(newFunc, x - 1)
        end
    end
    newV = FinFunction(newFunc, oldV.codom.set - 1)
    new_comp = (;Dict([(:V, newV, :E, f.components[:E])])...)
    return CSetTransformation(new_comp, new_dom, new_codom)

end
function rem_edge_codomain(f::CSetTransformation, n::Int)::CSetTransformation
    new_dom = deepcopy(f.dom)
    new_codom = deepcopy(f.codom)
    rem_edge!(new_codom, n)

    oldE = f.components[:E]
    newFunc = Int[]
    for x in oldE.func
        if x < n
            push!(newFunc, x)
        elseif x > n
            push!(newFunc, x - 1)
        end
    end
    newE = FinFunction(newFunc, oldE.codom.set - 1)
    new_comp = (;Dict([(:V, f.components[:V], :E, newE)])...)

    return CSetTransformation(new_comp, new_dom, new_codom)
end

function make_inclusion(src::Graph,tgt::Graph)::CSetTransformation
    return CSetTransformation(src, tgt, V=collect(1:nv(src)), E=collect(1:ne(src)))
end

"""
   l
L <-- I
|     |
|m    |d
v  <- D
G  g
Given I (interface), L, G (target graph to rewrite), m (match), l
Find d, g such that (L -m-> G <-g- D) is the pushout of (L <-l- I -d-> D)
"""
function pushout_complement(L::CSetTransformation,m::CSetTransformation)::Pair{CSetTransformation,CSetTransformation}
    k = compose(L, m)
    # Doing a mechanical thing for each component?   -> generalize to CSets?
    for e in orphan_edges(L)
        k = rem_edge_codomain(k, m[:E](e))
    end
    for n in orphan_nodes(L)
        k = rem_node_codomain(k, m[:V](n))
    end

    return k => make_inclusion(k.codom, m.codom)
end

function calc_pushout(r::CSetTransformation,k::CSetTransformation)::Pair{CSetTransformation,CSetTransformation}
    z = pushout(r, k)
    l1, l2 = z.cocone.legs
    return l1 => l2
end


function rewrite(L::CSetTransformation, R::CSetTransformation, m::CSetTransformation)::Graph
    (k, f) = pushout_complement(L, m)
    (g, n) = calc_pushout(R, k)
    return g.codom
end



"""
Find an inclusion graph homomorphism (if any exists). Return the first one found.
Adapted from Ullmann algorithm
"""
function match_pat(g::Graph, pat::Graph)::Union{Nothing,FinFunction}
    function search!(g::Graph,pat::Graph,asgmts::Vector{Int},poss_asgmts::Vector{Vector{Bool}})::Bool
        function update_poss_asgmts!(g::Graph, pat::Graph, poss_asgmts::Vector{Vector{Bool}})::Nothing
            any_changes = true
            while any_changes
              any_changes = false
              for i in 1:nv(pat)
                for j in findall(poss_asgmts[i])
                  for x in neighbors(pat,i)
                    match = any([y in findall(poss_asgmts[x]) && has_edge(g,j,y) for y in 1:nv(g)])
                    if !match
                      poss_asgmts[i][j] = false
                      any_changes = true
                    end
                  end
                end
              end
            end
          end
        update_poss_asgmts!(g,pat,poss_asgmts)
        curr_pat_node = length(asgmts)+1

        # Each edge btw assigned vertices in pat must be edge in g.
        for edge in edges(pat)
          if src(pat,edge)< curr_pat_node && tgt(pat,edge) < curr_pat_node
            if !has_edge(g,asgmts[src(pat,edge)],asgmts[tgt(pat,edge)])
              return false # failure
            end
          end
        end

        # If all the vertices in the subgraph are assigned, then we are done.
        if curr_pat_node == nv(pat) + 1
          return true # success
        end

        for poss_asgmt in findall(poss_asgmts[curr_pat_node])
            if !(poss_asgmt in asgmts)
              append!(asgmts, poss_asgmt)

              # Create a new set of poss asgmts, where graph node j is the only
              # possibility for the asgmt of subgraph node i.
              new_poss_asgmts = deepcopy(poss_asgmts)
              new_poss_asgmts[curr_pat_node] = [n == poss_asgmt for n in 1:nv(g)]

              if search!(g, pat, asgmts, new_poss_asgmts)
                return true
              end

              pop!(asgmts) # BACKTRACK
              poss_asgmts[curr_pat_node][poss_asgmt] = false
              update_poss_asgmts!(g, pat, poss_asgmts)
            end
        end
        return false
    end
    asgmts=Int[]
    poss_asgmts = [repeat([true], nv(g)) for _ in 1:nv(pat)]
    success = search!(g,pat,asgmts,poss_asgmts)
    return success ? FinFunction(asgmts, nv(g)) : nothing
end


end
