using Catlab.CategoricalAlgebra
using Catlab.Present
using Catlab.Theories
using Base.Iterators: product as cartprod
using Catlab.CategoricalAlgebra.FinSets: preimage
using Catlab.Graphs
using Catlab.Graphs.BasicGraphs: TheoryGraph

T = CSetTransformation  # for brevity

"""
Assume one diagram per vertex in G (first index is the start of paths)
Assume at most one cone per vertex in G (last index is the apex)
"""
struct FLS
    G::CSet      # a Graph, arrows are "operations"
    D::Vector{T} # diagrams i.e. morphisms to G.
    C::Vector{T} # apex + edges in G from apex
    function FLS(G::CSet,D::Vector{T},C::Vector{T})
      seen = Set()
      for tt in D
        start = tt[:V](1)
        @assert !(start in seen)
        push!(seen,start)
        @assert codom(tt) == G
        @assert is_natural(tt)
      end
      seen = Set()

      for tt in C
        cone = tt[:V](nv(dom(tt)))
        @assert !(cone in seen)
        push!(seen, cone)
        @assert codom(tt) == G
        @assert topological_sort(dom(tt))[1] == nv(dom(tt)) # apex is last
        @assert is_natural(tt)
      end
      return new(G,D,C)
    end
  end

@present TheoryFLSketch(FreeSchema) begin
    # Main Graph
    (V, E)::Ob
    (src, tgt)::Hom(E,V)

    # Diagrams
    (Dv, De)::Ob
    root::Hom(V, Dv)
    (dSrc, dTgt)::Hom(De,Dv)
    dV::Hom(Dv, V) # which vertex's diagram
    dE::Hom(De, V) # does this belong to?

    # Cones
    (Cone, Cv, Ce)::Ob
    (cSrc, cTgt)::Hom(Ce,Cv)
    cV::Hom(Cv, Cone)
    cE::Hom(Ce, Cone)
    apex::Hom(Cone, Cv)

    # Homorphisms data
    cvMap::Hom(Cv, V)
    ceMap::Hom(Ce, E)
    dvMap::Hom(Dv, V)
    deMap::Hom(De, E)

    # Diagrams/cones don't touch each other
    compose(apex, cV) == id(Cone)  # EQUATION ON CONE
    compose(cSrc, cV) == cE        # EQUATION ON Ce
    compose(cTgt, cV) == cE        # EQUATION ON Ce
    compose(dSrc, dV) == dE        # EQUATION ON De
    compose(dTgt, dV) == dE        # EQUATION ON De

    # Root of each diagram is the right vertex
    compose(root, dV) == id(V)  # EQUATION ON V

    # Homomorphism properties
    compose(deMap, src) == compose(dSrc, dvMap) # EQUATION ON De
    compose(deMap, tgt) == compose(dTgt, dvMap) # EQUATION ON De
    compose(ceMap, src) == compose(cSrc, cvMap) # EQUATION ON Ce
    compose(ceMap, tgt) == compose(cTgt, cvMap) # EQUATION ON Ce
end;

function add_srctgt(fk::Symbol, src::Bool)
    return Symbol(string(fk) * "_" * (src ? "src" : "tgt"))
end

# Make const once file is stable
if !isdefined(Main, :Fls)
const Fls = CSetType(TheoryFLSketch, index=[:src, :tgt, :dSrc, :dV, :dE]);
end

@present TheoryLabeledGraph <: TheoryGraph begin
  Label::Data
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end;
const LabeledGraph = ACSetType(TheoryLabeledGraph, index=[:src,:tgt],
                               ){Symbol};
# we don't want unique_index=[:vlabel, :elabel] because we want to use
# labels to specify homomorphisms which may not be injective

struct LabeledFLS
    fls::Fls
    labels::Pair{Vector{Symbol}, Vector{Symbol}} # label nodes and edges
end
function vi(fls::LabeledFLS, v::Symbol)::Int
    return findfirst(==(v), fls.labels[1])
end
function ei(fls::LabeledFLS, v::Symbol)::Int
    return findfirst(==(v), fls.labels[2])
end

"""
No cones, trivial diagrams
"""
function FLSinit(g::LabeledGraph)::LabeledFLS
    fls = Fls()
    add_parts!(fls, :V, nv(g))
    add_parts!(fls, :Dv, nv(g), dV=1:nv(g), dvMap=1:nv(g))
    add_parts!(fls, :E, ne(g))
    set_subpart!(fls, :src, g[:src])
    set_subpart!(fls, :tgt, g[:tgt])
    set_subpart!(fls, :root, 1:nv(g))
    return LabeledFLS(fls, g[:vlabel] => g[:elabel])
end

"""
Get the commutivity diagram of a FLS
"""
function get_diagram(fls::LabeledFLS, root::Symbol)::LabeledGraph
    res = LabeledGraph()
    f = fls.fls
    rooti = vi(fls, root)
    nodes = f.indices[:dV][rooti]
    edges = f.indices[:dE][rooti]
    nodedict = Dict([i=>e for (e, i) in enumerate(nodes)])
    vlab = [fls.labels[1][f[:dvMap][i]] for i in nodes]
    add_parts!(res, :V, length(nodes), vlabel=vlab)
    edata = [(e, f[:dSrc][e], f[:dTgt][e]) for e in edges]
    for (e, s, t) in edata
        elab = fls.labels[2][f[:deMap][e]]
        add_part!(res, :E, src=f[:dvMap][nodedict[s]], tgt=f[:dvMap][nodedict[t]], elabel=elab)
    end
    return res
end

"""Extract the underlying graph (no diagrams/cones)"""
function get_schema(fls::LabeledFLS)::LabeledGraph
    res = LabeledGraph()
    add_parts!(res, :V, length(fls.labels[1]), vlabel=fls.labels[1])
    add_parts!(res, :E, length(fls.labels[2]), src=fls.fls[:src], tgt=fls.fls[:tgt], elabel=fls.labels[2])
    return res
end
"""
Get all commuting paths starting at a particular node
"""
function all_paths(fls, root::Symbol)::Dict{Vector{Symbol}, Int}
    res = Dict{Vector{Symbol}, Int}()
    rooti = vi(fls, root)
    f = fls.fls
    rootind = f[:root][rooti]
    stack = Tuple{Int,Vector{Symbol}}[(rootind, [])]
    while !isempty(stack)
        currnode, currpath = pop!(stack)
        res[currpath] = currnode
        for e in f.indices[:dSrc][currnode]
            orig_e = f[:dE][e]
            e_symbol = fls.labels[2][orig_e]
            push!(stack, (f[:dTgt][e], vcat(currpath, [e_symbol])))
        end
    end

    return res
end

"""
Add a diagram where the first node is the root. Labels indicate homomorphism.
"""
function add_diagram!(fls::LabeledFLS, d::LabeledGraph)::Nothing
    rootless = LabeledGraph()
    add_parts!(rootless, :V, nv(d), vlabel=d[:vlabel])
    for (e, (ss, tt)) in enumerate(zip(d[:src], d[:tgt]))
        if tt != 1
            add_part!(rootless, :E, elabel=d[:elabel][e], src=ss, tgt=tt)
        end
    end
    topological_sort(rootless)  # must be acyclic, after removing loops to root
    root = d[:vlabel][1]
    rooti = vi(fls, root)
    # paths that already exist in the FLS
    location = all_paths(fls, root)
    f = fls.fls
    seen = Dict{Int, Int}() # index in d => index in FLS diagram
    # (index in d, index in FLS diagram, path in d)
    stack = Tuple{Int,Int,Vector{Symbol}}[(1, f[:root][rooti], Symbol[])]
    while !isempty(stack)
        dnode, currnode, currpath = pop!(stack)
        seen[dnode] = currnode
        vlabel = d[:vlabel][dnode]
        nextedges = d.indices[:src][dnode]
        for e in nextedges
            elab = d[:elabel][e]
            orig_edge = ei(fls, elab)
            nextpath = vcat(currpath, [elab])
            seenflag = false
            if haskey(location, nextpath)
                nextnode = location[nextpath]
            else
                next_d = d[:tgt][e]
                next_orig = vi(fls, d[:vlabel][next_d])
                if haskey(seen, next_d)
                    nextnode = seen[next_d]
                    seenflag=true
                else
                    nextnode = add_part!(f, :Dv, dV=rooti, dvMap=next_orig)
                end
                add_part!(f, :De, dSrc=currnode, dTgt=nextnode,
                dE=rooti, deMap=orig_edge)
            end
            if !seenflag
                push!(stack, (d[:tgt][e], nextnode, nextpath))
            end
        end
    end
end

"""
For p1=p2, if p1 is completely known but p2 is only known up to penultimate
value, then
"""
function propagate_diagram!(fls::LabeledFLS, cset::CSet)::Nothing
    return nothing
end

"""
If one leg of a base is completely known (we know the apex), then all
other legs should be determined.
"""
function propagate_cone!(fls::LabeledFLS, cset::CSet)::Nothing
    @assert false
    return nothing
end

"""
Return false if unsat

If # of cone bases is smaller than # of apex pks, we're unsat
"""
function check_cone(fls::LabeledFLS, cset::CSet)::Bool
    @assert false
    return true
end

"""
Create a linear sketch (no cones) based on a CSet presentation
"""
function catpres_to_linear(pres::Presentation)::LabeledFLS
    obs = pres.generators[:Ob]
    homs = pres.generators[:Hom]
    vlab = [x.args[1] for x in obs]
    odict = Dict([o => i for (i, o) in enumerate(obs)])
    idsymbs = [Symbol("_id_"*string(v)) for v in vlab]
    elab = vcat([x.args[1] for x in homs], idsymbs)
    # Create initial graph
    g = LabeledGraph()
    n, nh = length(vlab), length(homs)
    add_parts!(g, :V, n, vlabel=vlab)
    srcs = vcat([odict[h.type_args[1]] for h in homs], 1:n)
    tgts = vcat([odict[h.type_args[2]] for h in homs], 1:n)
    add_parts!(g, :E, nh+n, src=srcs, tgt=tgts, elabel=elab)
    fls = FLSinit(g)
    # Add diagrams
    for (p1, p2) in pres.equations
        d = paths_to_diagram(p1, p2)
        add_diagram!(fls, d)
    end
    return fls
end

function paths_to_diagram(p1, p2)::LabeledGraph
    d = LabeledGraph()
    root = p1.type_args[1].args[1]
    add_part!(d, :V, vlabel=root)
    function add_path!(start::Bool, p)::Nothing
        typ = typeof(p).parameters[1]
        if typ == :id
            if start
                tgt = add_part!(d, :V, vlabel=root)
            else
                tgt = nparts(d, :V)
            end
            elab = Symbol("_id_"*string(root))
            add_part!(d, :E, src=1, tgt=tgt, elabel=elab)
        elseif typ == :compose
            homs = p.args
            curr = 1
            if start
                last = length(homs) + 1
            else
                last = nparts(d, :V)
            end
            for (i, hom) in enumerate(homs)
                add_part!(d, :V, vlabel=hom.type_args[2].args[1])
                if i == length(homs)
                    tgt = last
                else
                    tgt = curr+1
                end
                add_part!(d, :E, src=curr, tgt=tgt, elabel=hom.args[1])
                curr += 1
            end
        elseif typ == :generator
            if start
                last = add_part!(d, :V, vlabel=p.type_args[2].args[1])
            else
                last = nparts(d, :V)
            end
            add_part!(d, :E, src=1, tgt = last, elabel=p.args[1])
        else
            @assert false "Not prepared for type $typ"
        end
        return nothing
    end
    add_path!(true, p1)
    add_path!(false, p2)
    return d
end

"""CSet type of the category of elements"""
function catelems(fls::LabeledFLS)::Type
    pres = Presentation(FreeSchema)
    nv = length(fls.labels[1])
    alledge = Symbol[]
    xobs = [Ob(FreeSchema, s) for s in vcat(collect(fls.labels)...)]
    for x in xobs
        add_generator!(pres, x)
    end
    for (i,(src, tgt)) in enumerate(zip(fls.fls[:src], fls.fls[:tgt]))
        s, t = [add_srctgt(fls.labels[2][i], x) for x in [true, false]]
        add_generator!(pres, Hom(s, xobs[nv+i], xobs[src]))
        add_generator!(pres, Hom(t, xobs[nv+i], xobs[tgt]))
        append!(alledge, [s,t])
    end
    return CSetType(pres, index=alledge)
end

"""Cset type associated with FLS graph"""
function fls_csettype(fls::LabeledFLS)::Type
    pres = Presentation(FreeSchema)
    xobs = [Ob(FreeSchema, s) for s in fls.labels[1]]
    for x in xobs
        add_generator!(pres, x)
    end
    for (isym,s, t) in zip(fls.labels[2], fls.fls[:src], fls.fls[:tgt])
        add_generator!(pres, Hom(isym, xobs[s], xobs[t]))
    end
    return CSetType(pres, index=fls.labels[2])
end
"""
Take a real CSet and construct category of elements with
exactly one FK value per PK
"""
function cset_to_catelems(fls::LabeledFLS, cset::CSet)::CSet
    res = catelems(fls)()
    for ob in fls.labels[1]
        add_parts!(res, ob, nparts(cset, ob))
    end
    for (i, ss) in enumerate(fls.fls[:src])
        isym = fls.labels[2][i]
        s, t = [add_srctgt(isym, x) for x in [true, false]]
        for src_ind in 1:nparts(cset, fls.labels[1][ss])
            args = Dict([s=>src_ind, t=>cset[isym][src_ind]])
            add_part!(res, isym; args...)
        end
    end
    return res
end

"""
Coerce a LABELED GRAPH diagram into the schema of the
category of elements.
"""
function dia_to_catelem(fls::LabeledFLS, dia::LabeledGraph)::CSet
    res = catelems(fls)()
    ref = Dict{Pair{Symbol, Int}, Int}()
    for (i, lab) in enumerate(dia[:vlabel])
        ind = add_part!(res, lab)
        ref[lab => i]=ind
    end
    for (e, ss, tt) in zip(dia[:elabel], dia[:src], dia[:tgt])
        slab, tlab = dia[:vlabel][[ss,tt]]
        s, t = [add_srctgt(e, x) for x in [true, false]]
        args = Dict([s => ref[slab => ss], t=> ref[tlab => tt]])
        add_part!(res, e; args...)
    end
    return res
end

"""Get the indices that satisfy equations starting at a particular node"""
function check_diagram(fls::LabeledFLS, catelem::CSet, sym::Symbol)::Set{Int}
    dia = dia_to_catelem(fls, get_diagram(fls, sym))
    hs = homomorphisms(dia, cset_to_catelems(fls, catelem))
    sat_inds = [h.components[sym](1) for h in hs]
    return Set(sat_inds)
end

"""Yes or no, does a CSet satisfy the diagrams of the FLS"""
function check_diagrams(fls::LabeledFLS, catelem::CSet, error::Bool=true)::Bool
    for s in fls.labels[1]
        sat_inds = check_diagram(fls, catelem, s)
        if length(sat_inds) != nparts(catelem, s)
            bad = sort(collect(setdiff(1:nparts(catelem,s), sat_inds)))
            if error
                @assert false "Equations for $s not satisfied by indices $bad"
            else
                return false
            end
        end
    end
    return true
end

"""
Given a CSet from a FreeSchema presentation (e.g. Reflexive Graph) and a CSet
(e.g. an arbitrary instance of Reflexive Graph) throw an error if the CSet
does not conform to the equations in the presentation.
"""
function check_diagrams(p::Presentation, cset::CSet)::Nothing
    fls = catpres_to_linear(p)
    catelem = cset_to_catelems(fls, cset)
    check_diagrams(fls, catelem, true)
    return nothing
end


"""Populate category of elements with all possible FKs"""
function allposs(fls::LabeledFLS, consts::Vector{Int})::CSet
    res = catelems(fls)()
    for (i, c) in enumerate(consts)
        add_parts!(res, fls.labels[1][i], c)
    end
    for (i, (s, t)) in enumerate(zip(fls.fls[:src], fls.fls[:tgt]))
        fs, ft = [add_srctgt(fls.labels[2][i], x) for x in [true, false]]
        for j in 1:consts[s]
            for k in 1:consts[t]
                args = Dict([fs => j, ft => k])
                add_part!(res, fls.labels[2][i]; args...)
            end
        end
    end
    return res
end

"""
Conflict directed backtracking - modify the variables that are the REASON for the unsat
"arc consistency" binary relation on variables. REVISE algorithm
"""
function search(fls::LabeledFLS,
                consts::Vector{Int},
                n::Int=-1,
                guess::Union{Nothing,CSet}=nothing;
            )::Vector{CSet}
    # initialize
    @assert all(x->x>=0, consts)
    @assert length(consts) == nv(fls.labels[1])
    seen, res = Set(), Set()
    init = guess===nothing ? init_grph(fls.G, consts) : guess

    function search_rec(cset::CSet, depth::Int)::Nothing
        if length(res) == n
            return nothing
        end

        if !check_diagrams!(fls, cset, false)
            return nothing
        end
        if !check_cone!(fls, cset)
            return nothing
        end
        propagate_diagram!(fls, cset)
        propagate_cone!(fls, cset)

        lens = n_fks(fls, cset)
        ((nmax, pkmax), tabmax) = findmax(map(x->isempty(x) ? (1,1) : findmax(x), lens))
        if minimum(map(x->isempty(x) ? 1 : minimum(x), lens)) < 1
            return nothing
        elseif nmax == 1
            push!(res, ncset)
        else
            for i in 1:nmax # split on the largest FK
                newer_cset, _ = choose(ncset, tabmax, pkmax, i)
                newhsh = canonical_hash(newer_cset)
                if !(newhsh in seen)
                    push!(seen, newhsh)
                    search_rec(newer_cset, depth+1)
                end
            end
        end
    return nothing
    end
    search_rec(init, 0)
    return collect(res)
end

"""
For each PK+FK combo, how many FKs are in the category of elements
"""
function n_fks(fls::LabeledFLS, cset::CSet)::Vector{Vector{Int}}
    return [x => cset.indices[add_srctgt(x, true)] for x in fls.labels[2]]
end