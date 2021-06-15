using Catlab.CategoricalAlgebra
using Catlab.Present
using Catlab.Theories
using Base.Iterators: product as cartprod
using Catlab.CategoricalAlgebra.FinSets: preimage
using Catlab.Graphs
using Catlab.Graphs.BasicGraphs: TheoryGraph
using DataStructures: OrderedDict

T = CSetTransformation  # for brevity

@present TheoryFLSketch(FreeSchema) begin
    # Main Graph
    (V, E)::Ob
    (src, tgt)::Hom(E,V)

    # Diagrams
    (Dv, De)::Ob
    root::Hom(V, Dv)
    (dSrc, dTgt)::Hom(De,Dv) # graph data of diagram
    dV::Hom(Dv, V) # which vertex's diagram
    dE::Hom(De, V) # does this belong to?

    # Cones
    (Cone, Cv, Ce)::Ob
    (cSrc, cTgt)::Hom(Ce,Cv)
    cV::Hom(Cv, Cone) # which Cone
    cE::Hom(Ce, Cone) # does this belong to
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

"""Append either _src or _tgt to a symbol"""
function add_srctgt(fk::Symbol, src::Bool)::Symbol
    return Symbol(string(fk) * "_" * (src ? "src" : "tgt"))
end
function add_srctgt(fk::Symbol)::Pair{Symbol, Symbol}
    return add_srctgt(fk, true) => add_srctgt(fk, false)
end

if !isdefined(Main, :Fls)
const Fls = CSetType(TheoryFLSketch, index=[:src, :tgt, :dSrc, :dV, :dE, :cV, :cE]);
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

"""Annotate a FLS CSet with labels"""
struct LabeledFLS
    fls::Fls
    labels::Pair{Vector{Symbol}, Vector{Symbol}} # label nodes and edges
end

"""Access vertex labels of graph underlying FLS"""
function vi(fls::LabeledFLS, v::Symbol)::Int
    return findfirst(==(v), fls.labels[1])
end

"""Access edge labels of graph underlying FLS"""
function ei(fls::LabeledFLS, v::Symbol)::Int
    return findfirst(==(v), fls.labels[2])
end

"""No cones, trivial diagrams"""
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

"""Get the commutivity diagram of a FLS"""
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
        add_part!(res, :E, src=nodedict[s], tgt=nodedict[t], elabel=elab)
    end
    return res
end

"""Get cone or just the base of of the cone"""
function get_cone(fls::LabeledFLS, apex::Symbol, base::Bool=false)::Union{Nothing, LabeledGraph}
    f = fls.fls
    apexes = fls.labels[1][f[:cvMap][f[:apex]]]
    cone_ind = findfirst(==(apex), apexes)
    if cone_ind === nothing
        return nothing
    end
    res = LabeledGraph()
    cv, ce = [f.indices[x][cone_ind] for x in [:cV, :cE]]
    reind = [findfirst(==(i), cv) for i in 1:maximum(cv)]
    vlab = fls.labels[1][f[:cvMap][cv]]
    elab = fls.labels[2][f[:ceMap][ce]]
    add_parts!(res, :V, length(cv), vlabel=vlab)
    add_parts!(res, :E, length(ce), elabel=elab, src=reind[f[:cSrc][ce]],tgt=reind[f[:cTgt][ce]])
    if base
        rem_part!(res, :V, nv(res))
        rem_parts!(res, :E, [e for (e, s) in enumerate(res.tables[:E]) if s[:src] == 0])
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

"""Get all commuting paths starting at a particular node"""
function all_paths(fls, root::Symbol)::OrderedDict{Vector{Symbol}, Int}
    res = OrderedDict{Vector{Symbol}, Int}()
    rooti = vi(fls, root)
    f = fls.fls
    rootind = f[:root][rooti]
    stack = Tuple{Int,Vector{Symbol}}[(rootind, [])]
    seen = Set()
    while !isempty(stack)
        currnode, currpath = pop!(stack)
        res[currpath] = currnode
        if !(currnode in seen)
            push!(seen, currnode)
            for e in f.indices[:dSrc][currnode]
                orig_e = f[:deMap][e]
                e_symbol = fls.labels[2][orig_e]
                nextnode = f[:dTgt][e]
                push!(stack, (nextnode, vcat(currpath, [e_symbol])))
            end
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

function add_cone!(fls::LabeledFLS, c::LabeledGraph)::Nothing
    f = fls.fls
    conetgt = vi(fls, c[:vlabel][end])
    prevcones = f[:cvMap][f[:apex]]
    @assert !(conetgt in prevcones) "No more than one cone on a given vertex"
    cone_id = add_part!(f, :Cone)
    vert_ids = add_parts!(f, :Cv, nv(c), cV=cone_id, cvMap=[vi(fls, l) for l in c[:vlabel]])
    emap = [ei(fls, l) for l in c[:elabel]]
    esrc = vert_ids[c[:src]]
    etgt = vert_ids[c[:tgt]]
    add_parts!(f, :Ce, ne(c), cE=cone_id, ceMap=emap, cSrc=esrc, cTgt=etgt)
    set_subpart!(f, cone_id, :apex, vert_ids[end])
    return nothing
end
"""
For p1=p2, if p1 is completely known but p2 is only known up to penultimate
value, then
"""
function propagate_diagram!(fls::LabeledFLS, cset::CSet)::Nothing
    for sym in fls.labels[1]
        propagate_diagram!(fls, cset, sym)
    end
    return nothing
end

"""
Use diagrams to rule out certain possibilities
"""
function propagate_diagram!(fls::LabeledFLS, cset::CSet, sym::Symbol)::Nothing
    paths = all_paths(fls, sym)
    verts = sort(collect(Set(values(paths))))
    vertsyms = [fls.labels[1][fls.fls[:dvMap][v]] for v in verts]
    to_delete = Dict{Symbol, Set{Int}}([l=>Set{Int}() for l in fls.labels[2]])
    vals = Dict{Vector{Symbol},Vector{Set{Int}}}([Symbol[] => Set{Int}[Set{Int}([i]) for i in 1:nparts(cset, sym)]])
    for (p, _) in filter(x->!isempty(x[1]), paths)
        tail, head = p[1:end-1], p[end]
        head_src, head_tgt = add_srctgt(head)
        valsp = Set{Int}[union([Set{Int}(
            cset[head_tgt][cset.indices[head_src][i]]) for i in iset]...)
                   for iset in vals[tail]]
        vals[p] = valsp
    end
    # for each junction, check if any of the penultimate nodes is completely determined
    junctions = filter(x-> count(==(x[1]), values(paths)) > 1 , collect(zip(verts, vertsyms)))
    for (j, jsym) in junctions
        jpaths = [p for (p, v) in collect(paths) if v == j]
        for i in 1:nparts(cset, jsym)  #consider paths starting at each elem of component
            alljvals = [vals[jpath][i] for jpath in jpaths]
            jvals = union(Set{Int}(), [jv for jv in alljvals if length(jv)==1]...)
            #println("J $j $jsym#$i jpaths $jpaths alljvals $alljvals jvals $jvals\n$cset")
            #println("$(check_diagrams(fls, cset, false; cset_is_catelem=true))")
            @assert length(jvals) in [0, 1]
            if !isempty(jvals) # we know what value to set this path equal to
                jval = pop!(jvals)
                # can only use this info if the PENULTIMATE path is unambiguous
                for jpath in filter(!isempty, jpaths)
                    tail, head = jpath[1:end-1], jpath[end]
                    head_src, head_tgt = add_srctgt(head)
                    if length(vals[tail][i])==1
                        penult_val = collect(vals[tail][i])[1]
                        # keep just the FK that goes to jval
                        all_fks = cset.indices[head_src][penult_val]
                        bad_fks = [fk for fk in all_fks if cset[head_tgt][fk] != jval]
                        union!(to_delete[head], Set(bad_fks))
                    end
                end
            end
        end
    end
    rem!(cset, to_delete)
end


"""
If one leg of a base is completely known (we know the apex), then all
other legs should be determined.
"""
function propagate_cone!(fls::LabeledFLS, cset::CSet)::Nothing
    return nothing
end

"""
Return false if unsat

Demand that every apex has at least one base (# of bases could
potentially decrease as we remove FKs).

If the legs have been finalized, then we demand every apex has
exactly one base

For apexes that have been finalized (have a determinate base)
then we check that these are unique.
"""
function check_cone(fls::LabeledFLS, cset::CSet)::Bool
    for sym in fls.labels[1]
        if !check_cone(fls, cset, sym)
            return false
        end
    end
    return true
end
function check_cone(fls::LabeledFLS, cset::CSet, apx::Symbol)::Bool
    cone = get_cone(fls, apx, false)
    base = get_cone(fls, apx, true)
    n = nparts(cset, apx)
    if base === nothing
        return true
    end
    basefinal = check_base_final(fls, cset, base)
    basedia = dia_to_catelem(fls, base)
    matches = [h.components for h in homomorphisms(basedia, cset)]
    if basefinal && length(matches) != n
        # println("base is final but $(length(matches)) != # of apexes ($n)")
        return false
    end
    apexes = [get_apexes(cset, apx, cone, h) for h in matches]
    all_apexes = union(Set{Int}(), apexes...)
    cover = length(all_apexes) == n
    if !cover
        return false
    end
    seen_base = Set()
    for i in 1:n
        known_base = []
        known = true
        for e in cone.indices[:src][nv(cone)]
            esrc, etgt = add_srctgt(cone[:elabel][e])
            leg = cset[etgt][cset.indices[esrc][i]]
            if length(leg) == 1
                push!(known_base, leg[1])
            else
                known = false
                break
            end
        end
        if known
            if known_base in seen_base
                # println("Duplicate base")
                return false
            else
                push!(seen_base, known_base)
            end
        end
    end
    return true
end

"""Check if every edge in a diagram is fully determined in a
category of elements"""
function check_base_final(fls, cset, base)::Bool
    ns = n_fks(fls, cset)
    for e in Set(base[:elabel])
        for n in ns[e]
            if n != 1
                return false
            end
        end
    end
    return true
end
"""Return potential apexes for a given base"""
function get_apexes(cset::CSet, apx::Symbol, cone::ACSet, morph)::Set{Int}
    poss_apex_inds = Set(1:nparts(cset, apx))
    for e in cone.indices[:src][nv(cone)]
        esrc, etgt = add_srctgt(cone[:elabel][e])
        tgt = cone[:tgt][e]
        tgt_sym = cone[:vlabel][tgt]
        tgt_ind = findfirst(==(tgt), [i for (i,s) in enumerate(cone[:vlabel]) if s == tgt_sym])
        tgt_in_cset = morph[tgt_sym](tgt_ind)
        intersect!(poss_apex_inds, cset[esrc][cset.indices[etgt][tgt_in_cset]])
    end
    return poss_apex_inds
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

"""Create a diagram from a path equality"""
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
        s, t = add_srctgt(fls.labels[2][i])
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
        s, t = add_srctgt(isym)
        for src_ind in 1:nparts(cset, fls.labels[1][ss])
            sym = string(isym)
            tval = length(sym)>3 && sym[1:4] == "_id_" ? src_ind : cset[isym][src_ind]
            args = Dict([s=>src_ind, t=>tval])
            add_part!(res, isym; args...)
        end
    end
    return res
end

function catelems_to_cset(fls::LabeledFLS, catelems::CSet)::CSet
    res = fls_csettype(fls)()
    for v in fls.labels[1]
        add_parts!(res, v, nparts(catelems, v))
    end
    for e in fls.labels[2]
        esrc, etgt = add_srctgt(e)
        evec = catelems[etgt][[x[1] for x in catelems.indices[esrc]]]
        set_subpart!(res, e, evec)
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
        s, t = add_srctgt(e)
        args = Dict([s => ref[slab => ss], t=> ref[tlab => tt]])
        add_part!(res, e; args...)
    end
    return res
end

"""Get the indices that satisfy equations starting at a particular node"""
function check_diagram(fls::LabeledFLS, cset::CSet, sym::Symbol; cset_is_catelem::Bool=false)::Set{Int}
    cset_ = cset_is_catelem ? cset : cset_to_catelems(fls, cset)
    dia = dia_to_catelem(fls, get_diagram(fls, sym))
    hs = homomorphisms(dia, cset_)
    sat_inds = [h.components[sym](1) for h in hs]
    return Set(sat_inds)
end

"""Yes or no, does a CSet satisfy the diagrams of the FLS"""
function check_diagrams(fls::LabeledFLS, catelem::CSet, error::Bool=true; cset_is_catelem::Bool=false)::Bool
    for s in fls.labels[1]
        sat_inds = check_diagram(fls, catelem, s, cset_is_catelem=cset_is_catelem)
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
        fs, ft = add_srctgt(fls.labels[2][i])
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
    @assert length(consts) == length(fls.labels[1])
    seen, res = Set(), Set()
    init = guess===nothing ? allposs(fls, consts) : guess

    function search_rec(cset::CSet, depth::Int)::Nothing
        if length(res) == n
            return nothing
        end

        if !check_diagrams(fls, cset, false; cset_is_catelem=true)
            return nothing
        end
        if !check_cone(fls, cset)
            return nothing
        end
        old = deepcopy(cset)
        propagate_diagram!(fls, cset)
        if cset!=old
            hsh = canonical_hash(cset)
            if hsh in seen
                return nothing
            else
                push!(seen, hsh)
                old = deepcopy(cset)
            end
        end
        propagate_cone!(fls, cset)
        if cset!=old
            hsh = canonical_hash(cset)
            if hsh in seen
                return nothing
            else
                push!(seen, hsh)
            end
        end

        lens = filter(x->!isempty(x[2]), n_fks(fls, cset))  # [ida=>[1,2], f=>[3,2,1], g=>0, etc.]
        maxes = [k=>findmax(v) for (k, v) in collect(lens)]
        mins = [minimum(v) for (_, v) in collect(lens)]
        nmax = maximum([x[1] for (_, x) in maxes])

        if minimum(mins) < 1
            return nothing
        elseif nmax == 1
            push!(res, cset)
        else
            emax, maxind = [(k, v[2]) for (k, v) in maxes if v[1] == nmax][1]
            for i in 1:nmax # split on the largest FK
                newer_cset = choose(cset, maxind, emax, i)
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
For each PK+FK combo, how many FKs have that source
"""
function n_fks(fls::LabeledFLS, cset::CSet)::Dict{Symbol, Vector{Int}}
    res = Dict{Symbol, Vector{Int}}()
    for edge_sym in fls.labels[2]
        fks = map(length, cset.indices[add_srctgt(edge_sym, true)])
        res[edge_sym] = fks
    end
    return res
end

"""
Remove elements from tables - does not change any fk indices
so is only valid for tables which have no arrows to them
OR removing the LAST indices of a table
"""
function rem!(orig::CSet, rem::Dict{Symbol, Set{Int}})::Nothing
    for (comp, reminds) in collect(rem)
        rem_parts!(orig, comp, sort(collect(reminds)))
    end
    return nothing
end
"""Single table version of `rem`"""
function rem!(orig::CSet, tab::Symbol, rem::Set{Int})::Nothing
    rem_parts!(orig, tab, sort(collect(rem)))
    return nothing
end

"""Eliminate options from a model CSet by choosing a particular
FK combination for a specified PK."""
function choose(orig::CSet{CD}, srcind::Int, fk::Symbol, choice::Int)::CSet{CD} where {CD}
    fksrc = add_srctgt(fk, true)
    fks = orig.indices[fksrc][srcind]
    @assert 0 < choice <= length(fks)
    chosen = fks[choice]
    delinds = Set([fk for fk in fks if fk != chosen])
    res = deepcopy(orig)
    rem!(res, fk, delinds)
    return res
end
