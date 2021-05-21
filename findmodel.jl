
#------------------------------------------------
# ENUMERATING ALL MODELS PROJECT
#------------------------------------------------

# Goals:
# [x] Find out how to compute the canonical labeling of a CSet (nauty can't do multi digraphs)
# [x] Add impact of cones to model finding
# [ ] Need a data structure for sketches *defined* as colimits
# [ ] Figure out theoretically how the models are related
# [ ] Work out a database representation of all models found
# [ ] take advantage of colimit substructure
#   - i.e. how to get the enumeration for BIG models given the enumeration of smaller models?
#   - can then solve general problem in 2 steps
#   - 1: compute required models for sub-theories
#   - 2: combine and add stuff as necessary
# [ ] Less important: debug initial term model finding algorithm


"""
Given all the diagrams, which paths (given by pairs of edge sequences) must commute?
"""
function comm_paths(fls::FLSketch)::Set{Pair{Vector{Int}}}
    """Find all paths in a particular diagram"""

    function cp(m::ACSetTransformation)::Set{Pair{Vector{Int}}}
        d = m.dom
        M = m.components[:E]

        # Store set of paths between each pair of vertices
        # Also store set of
        paths = Dict{Pair{Int},Set{Pair{Vector{Int},Set{Int}}}}([
            (i=>j)=>Set() for i in 1:nv(d) for j in 1:nv(d)])

        # Initialize paths with edges
        for e in 1:ne(d)
            s, t = d[:src][e], d[:tgt][e]
            push!(paths[s => t], [e] => Set([s,t])) # also keep track of 'seen' nodes
        end

        # iteratively combine paths until convergence
        changed = true
        while changed
            changed = false
            for i in 1:nv(d)
                for j in 1:nv(d)
                    fs = paths[i=>j]
                    for k in 1:nv(d)
                        gs = paths[j=>k]
                        fgs = paths[i=>k]
                        for (f, fseen) in fs
                            for (g, gseen) in gs
                                ijk = i!=j || j!= k
                                no_repeat_nodes = intersect(fseen, gseen) == Set(i==k ? [i,j] : [j])
                                if ijk && no_repeat_nodes
                                    comp = vcat(f,g) => union(fseen, gseen)
                                    # NO DUPLICATES
                                    if !(comp in fgs)
                                        changed = true
                                        push!(paths[i=>k], comp )
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
        # collect all pairs
        pairs = []
        for (ij, pths) in collect(paths)
            pths = collect(pths)  # Set -> Vector
            if ij[1] == ij[2]
                for (f,_) in pths
                    push!(pairs, f=>Int[])  # loops equal to empty path
                end
            else
                for ((f,_),(g,_)) in zip(pths,pths[2:end])  # a=b,b=c,c=d...
                    push!(pairs, f=>g)
                end
            end
        end
        return Set(map(x->M(x[1])=>M(x[2]), pairs))
    end
    return isempty(fls.D) ? Set{Pair{Vector{Int}}}() : union(map(cp, collect(fls.D))...)
end

"""
General plan for enumeration:
1. Enumerate elements of ℕᵏ for an underlying graph with k nodes.
2. For each of these: (c₁, ..., cₖ), create a term model with that many constants

Do the first enumeration by incrementing n_nonzero
    and finding partitions so that ∑(c₁,...) = n_nonzero

In the future, this function will write results to a database
that hashes the FLS as well as the set of constants that generated the model.
"""
function enum(fls::FLSketch, n::Int)::Dict{Tuple,Vector{CSet}}
    res = Dict{Tuple,CSet}()
    n_const = 0 # total number of constants across all sets
    n_v = nv(fls.G)
    while length(res) < n
        n_const += 1
        for n_nonzero in 1:n_v
            # values we'll assign to nodes
            c_parts = partitions(n_const, n_nonzero)
            # Which nodes we'll assign them to
            indices = permutations(1:n_v,n_nonzero)

            for c_part in c_parts
                for index_assign in indices
                    n_const = zeros(n_v)
                    n_const[index_assign] = c_part
                    n_c = tuple(n_const...)
                    if !(n_c in res)
                        res[n_c] =  term_models(flv, n_c)
                    end
                end
            end
        end
    end
end

function xs(x::Int)::Symbol
    return Symbol("x$x")
end
function xs(xx::AbstractVector{Int})::Vector{Symbol}
    return [Symbol("x$x") for x in xx]
end
function es(x::Int)::Symbol
    return Symbol("e$x")
end
function es(xx::AbstractVector{Int})::Vector{Symbol}
    [Symbol("e$x") for x in xx]
end




"""
Create a CSet type specified by a graph
Vertices are x₁,x₂,..., edges are e₁, e₂,...
all edges are indexed
"""
function graph_to_cset(grph::CSet)::Type
    pres = Presentation(FreeSchema)
    xobs = [Ob(FreeSchema,xs(i)) for i in 1:nv(grph)]
    for x in xobs
        add_generator!(pres, x)
    end
    for (i,(src, tgt)) in enumerate(zip(grph[:src], grph[:tgt]))
        add_generator!(pres, Hom(es(i), xobs[src], xobs[tgt]))
    end
    return CSetType(pres, index=es(1:ne(grph)))
end

"""
Take in a Graph CSet, return wiring diagram Cset that
queries a CSet with the schema generated by `graph_to_cset` above

Actually use morphism which renames objects and edges, in case
d is a pattern to be interpreted in the context of another graph
"""
function diagram_to_query(m::ACSetTransformation)
    d  = m.dom
    xtgts = [Symbol("x$(m.components[:V](i))") for i in 1:nv(d)]
    xnames = [Symbol("$(x)_$i") for (i, x) in enumerate(xtgts)]
    enames = [Symbol("e$(m.components[:E](i))") for i in 1:ne(d)]
    rel = RelationDiagram{Symbol}(nv(d),port_names=xnames) # port_names=xtgts
    add_junctions!(rel, nv(d),variable=xnames)
    set_subpart!(rel, 1:nv(d), :outer_junction, 1:nv(d))
    for v in 1:nv(d)
        outarrows = d.indices[:src][v]
        b = add_box!(rel, 1+length(outarrows), name=xtgts[v])
        ps = ports(rel, b)
        set_subpart!(rel, ps, :port_name, vcat([:_id],enames[outarrows]))
        set_junction!(rel, ps, vcat([v],d[:tgt][outarrows]))
    end
    return rel
end

"""
Given two paths, [a₁,a₂,...] and [b₁, b₂,...] we want a query that
returns the penultimate and final nodes values along both paths
for each element in the source table, src(a₁)=src(b₁).
"""
function paths_to_query(d::ACSet, p1::Vector{Int}, p2::Vector{Int})
    n1, n2 = map(length, [p1, p2])
    res = [Symbol("$s$i") for s in ["pen", "last"] for i in 1:2]
    rel = RelationDiagram{Symbol}(4,port_names=res)
    root = add_box!(rel, n2 > 0 ? 3 : 2, name=xs(d[:src][p1[1]]))
    ps = ports(rel, root)
    add_junctions!(rel, 1, variable=[:init])
    set_junction!(rel, [ps[1]], [1])
    set_subpart!(rel, ps[1], :port_name, :_id)

    for (p_index,path) in [1=>p1, 2=>p2]
        if isempty(path)

        else
            outport = ps[p_index+1]
            lastj, = add_junctions!(rel, 1, variable=[Symbol("p_$(p_index)_1")])
            set_junction!(rel, [outport], [lastj])
            for (i, arr) in enumerate(path)
                set_subpart!(rel, outport, :port_name, es(arr))
                if i < length(path)
                    j, = add_junctions!(rel, 1, variable=[Symbol("p_$(p_index)_$(i+1)")])
                    b = add_box!(rel, 2, name=xs(d[:tgt][arr]))
                    pid, pout = ports(rel, b)
                    set_subpart!(rel, pid, :port_name, :_id)
                    set_junction!(rel, [pid,pout], [lastj, j])
                    outport = pout
                    lastj = j
                end
            end
        end
    end
    set_subpart!(rel, 1:4, :outer_junction, [
        n1, n2 < 2 ? 1 : n1+n2, n1+1, n2 == 0 ? 1 : n1+n2+1])
    return rel
end

"""
Helper function to get the penultimate and
last tables of a pair of commutative paths
(note we only allow p2 to be empty)
"""
function lasttabs(d::ACSet, p1::Vector{Int}, p2::Vector{Int})::Vector{Int}
    root =d[:src][p1[1]]
    penult_1, last_1 = [d[x][p1[end]] for x in [:src, :tgt]]
    penult_2 = isempty(p2) ? root : d[:src][p2[end]]
    last_2 = isempty(p2) ? root : d[:tgt][p2[end]]
    @assert last_1 == last_2
    return [penult_1, penult_2, last_1, last_2]
end


"""
Everything we know about a partial-information model

Because items can be added to the target in the future,
we must record which values we have considered.
"""
struct Model
    src::Vector{Int}
    tgt::Vector{Int}
    tables::Vector{IntDisjointSets}
    fks::Vector{Vector{Int}}
    pks::Vector{Vector{Int}} # which id's are primary
    considered::Vector{Vector{Set{Int}}} # which alternative vals we've already split this FK on
end

@present TheoryModel(FreeSchema) begin
  (Elem, Obj, PK, FK, HomElem, Considered)::Ob
  eo::Hom(Elem, Obj)
  po::Hom(PK, Obj)
  pe::Hom(PK, Elem)
  (src, tgt)::Hom(FK, Obj)
  hefk::Hom(HomElem, FK)
  hesrc::Hom(HomElem, PK)
  hetgt::Hom(HomElem, Elem)
  che::Hom(Considered, HomElem)
  cpk::Hom(Considered, PK)
end

const CombModel = ACSetType(TheoryModel, index=[:eo,:po,:pe,:src,:tgt,:hefk,:hesrc,:hetgt,:che,:cpk]);

function Base.length(m::Model)::Int
    return length(m.tables)
end

"""Encode Model as a CSet"""
function to_combinatorial(mod::Model)::CSet
    res = CombModel()
    add_parts!(res,:Obj, length(mod))
    add_parts!(res,:FK,length(mod.src))
    set_subpart!(res, :src, mod.src)
    set_subpart!(res, :tgt, mod.tgt)
    srcarrs = [[e for (e, src) in enumerate(mod.src) if src==i]
               for i in 1:length(mod)]
    pkdata = Dict{Int,Tuple{Int,Int,Int,Dict{Int,Int}}}[]
    for tab in 1:length(mod)
        pk_unique = Dict()
        for (i, pk) in enumerate(mod.pks[tab])
            pk_id = mod.tables[tab].parents[pk]
            if !haskey(pk_unique, pk_id)
                cset_pk_id = add_part!(res, :PK)
                cset_pk_elem_id = add_part!(res, :Elem)
                set_subpart!(res, cset_pk_id, :po, tab)
                set_subpart!(res, cset_pk_elem_id, :eo, tab)
                set_subpart!(res, cset_pk_id, :pe, cset_pk_elem_id)

                fks = Dict{Int,Int}()
                for arr in srcarrs[tab]
                    fks[arr] = add_part!(res, :HomElem)
                    set_subpart!(res, fks[arr], :hefk, arr)
                    set_subpart!(res, fks[arr], :hesrc, cset_pk_id)
                end
                pk_unique[pk_id] = (i, cset_pk_id, cset_pk_elem_id, fks)
            end
        end
        push!(pkdata, pk_unique)
    end
    for (tab, pkdatas) in enumerate(pkdata)
        for (_, (orig_index,_,_,fks)) in collect(pkdatas)
            for arr in srcarrs[tab]
                tgt = mod.tgt[arr]
                homelem = fks[arr]
                raw_fk = mod.fks[tgt][orig_index]
                tgt_class = mod.tables[tgt].parents[raw_fk]
                if haskey(pkdata[tgt],tgt_class)
                    println("tgt $tgt pkdata $tgt_class ", pkdata[tgt])
                    println(pkdata[tgt][tgt_class])
                    tgt_elem_id = pkdata[tgt][tgt_class][3]
                else
                    tgt_elem_id = add_part!(res, :Elem)
                    set_subpart!(res, tgt_elem_id, :eo, tgt)
                end
                set_subpart!(res, homelem, :hetgt, tgt_elem_id)
            end
        end
    end

    # Considered
    for (fk, considereds) in enumerate(mod.considered)
        source, target = mod.src[fk], mod.tgt[fk]
        for (pk_index, considered) in enumerate(considereds)
            if haskey(pkdata[source], pk_index)
                hom_elem_id = pkdata[source][pk_index][4][fk]
                for cons in considered
                    raw_considered_elem = mod.pks[target][cons]
                    con_class = mod.tables[target].parents[raw_considered_elem]
                    pk_id = pkdata[target][con_class][2]
                    con_id = add_part!(res, :Considered)
                    set_subpart!(res, con_id, :cpk, pk_id)
                    set_subpart!(res, con_id, :che, hom_elem_id)
                end
            end
        end
    end
    return res
end

"""
Parse a CSet. This is not a strict inverse to to_combinatorial
but the pair forms an involution. `from` will discard elements
in the union-find that are not referred to by any PK or FK,
thereby collapsing things known to be equal.
"""
function from_combinatorial(mod::CSet)::Model
    src, tgt = mod[:src], mod[:tgt]
    elem_offset, tables, pks, fks, cons = [0], [], [], [], []
    for x in mod.indices[:eo]
        push!(tables, IntDisjointSets(length(x)))
        push!(elem_offset, elem_offset[end]+length(x))
    end
    for tab in length(tables)
        push!(pks, [pk-elem_offset[tab] for pk in mod.indices[:po][tab]])
    end
    for (fk_id, (srctab, tgttab)) in enumerate(zip(src, tgt))
        homelems = Set(mod.indices[:hefk][fk_id])
        fk_vect, con_vect = [], []

        for pk in pks[srctab]
            hes = filter(x->x in homelems, mod.indices[:hesrc][pk])
            @assert length(hes) == 1
            he = hes[1]
            push!(fk_vect, mod[:hetgt][he]+elem_offset[tgttab])
            consids = mod[:cpk][mod.indices[:che][he]]
            push!(con_vect, Set([c + elem_offset[tgttab] for c in consids]))
        end
        push!(fks, fk_vect)
        push!(cons, con_vect)
    end

    return Model(src, tgt, tables, fks, pks, cons)
end

function Base.show(io::IO, ::MIME"text/plain",mod::Model)
    show(io, "Mod($([show(t.parents) for t in mod.tables]), fk=$([show(fk) for fk in mod.fks]), pk=$([pk for pk in mod.pks]))")
end

function Base.show(io::IO, ::MIME"text/plain",mod::Model)
    show(io, "Mod($([t.parents for t in mod.tables]), fk=$([fk for fk in mod.fks]), pk=$([pk for pk in mod.pks]))")
end

function str(m::Model)::String
    io = IOBuffer();
    show(IOContext(io, :limit => true, :displaysize => (20, 40)), "text/plain", m);
    return  String(take!(io));
end

function Model(schema::CSet, consts::Vector{Int})::Model
    return Model(schema[:src], schema[:tgt], consts)
end

function Model(src::Vector{Int}, tgt::Vector{Int}, consts::Vector{Int})::Model
    pks = [collect(1:i) for i in consts]
    fks = [Vector{Int}() for _ in 1:length(src)]
    considered = [[Set{Int}() for _ in 1:consts[s]] for s in src]
    tabls = []
    for tab in 1:length(consts)
        counter = consts[tab]
        tgt_edges = [i for i in 1:length(src) if tgt[i]==tab]
        for e in tgt_edges
            for _ in 1:consts[src[e]]
                counter+=1
                push!(fks[e], counter)
            end
        end
        push!(tabls, IntDisjointSets(counter))
    end
    return Model(src,tgt,tabls, fks, pks, considered)
end

function to_graph(m::Model)::CSet
    schema = Graph(length(m.tables))
    add_edges!(schema, m.src, m.tgt)
    return schema
end

"""
loses the "considered" information, but organizes the
data in a way amenable to conjunctive queries / visualization

If sat, then we assume all FKs are matched, so we do
not need to create an extra "unknown" value per table
"""
function to_cset(m::Model, sat::Bool=false)::CSet

    res = graph_to_cset(to_graph(m))()
    for (tab, pks) in enumerate(m.pks)
        add_parts!(res, xs(tab), length(pks)+(sat ? 0 : 1))
    end
    for (arr, fks) in enumerate(m.fks)
        tgt_tab = m.tgt[arr]
        vals = [get_pk(m, tgt_tab, fkval) - (sat ? 1 : 0) for fkval in fks]
        # for arr in src_edges
        #     vals = [get_pk(m, arr, pk) - (sat ? 1 : 0) for pk in pks]
        set_subpart!(res, es(arr), vcat(sat ? Int[] : [1], vals))
        #end
    end
    return res
end

"""Check whether there are any unknown values"""
function is_sat(mod::Model)::Bool
    for (edge, fk_vect) in enumerate(mod.fks)
        tab = mod.tgt[edge]
        for fk_elem in fk_vect
            if !any(map(pk->in_same_set(mod.tables[tab], pk, fk_elem), mod.pks[tab]))
                return false
            end
        end
    end
    return true
end

"""
Returns PK WITH OFFSET (1 represents unknown PK)
Does not check if model is well-formed, i.e. if a FK
is connected to two PKs
"""
function get_pk(mod::Model, tab::Int, val::Int)::Int
    for (pk, pkval) in enumerate(mod.pks[tab])
        if in_same_set(mod.tables[tab], pkval, val)
            return pk+1
        end
    end
    return 1
end

# Add an element to a table.
function Base.push!(modl::Model, tab::Int)::Int
    # Add a new item in the target table and link to PK
    newval = push!(modl.tables[tab])
    push!(modl.pks[tab], newval)
    # For each table tab points to, add a new element for the FK val
    src_arrs = [e for (e, srctab) in enumerate(modl.src) if srctab == tab]
    for arr in src_arrs
        tgt = modl.tgt[arr]
        fkval = push!(modl.tables[tgt])
        push!(modl.fks[arr], fkval)
    end
    return newval
end

MAXSIZE=2

"""
Union two elements of table `tab`

"""
function union_fk!(mod::Model, tab::Int, fk1::Int, val1::Int, fk2::Int, val2::Int)::Nothing
    # println("mod $mod\ntab $tab\n1: fk$fk1 v$val1\n2: fk$fk2 $val2")
    v1 = mod.fks[fk1][val1]
    if fk2 == 0
        v2 = mod.pks[tab][val2]
    else
        v2= mod.fks[fk2][val2]
    end
    union!(mod.tables[tab], v1, v2)
    return nothing
end

function size(mod::Model)::Int
    return sum(map(length,mod.pks))
end

function Base.hash(mod::Model)::UInt64
    # return hash((mod.src, mod.tgt, mod.tables, mod.fks, mod.pks, mod.considered))
    m = to_cset(mod)
    return canonical_hash(m)
end

"""
Fill out any info we can from diagrams, detect contradiction
"""
function check_diagrams!(mod::Model, comm_data)::Pair{Bool,Bool}
    cset = to_cset(mod)
    change = false
    for (comm_q, (pth1, pth2)) in comm_data
        end_table = mod.tgt[pth1[end]]
        # println("query result $(query(cset, comm_q))")
        for qres in query(cset, comm_q)
            penult1, penult2, last1, last2 = qres
            nullp1, nullp2, null1, null2 = [qv == 1 for qv in qres]
            if !(nullp2 || nullp1) && (null1 || null2)  # can propagate info
                union_fk!(mod, end_table,
                          pth1[end], # the last edge in path 1
                          penult1-1,   #
                          isempty(pth2) ? 0 : pth2[end], # last edge in path 2 if any
                          penult2-1)
                change = true
            elseif !(null1||null2)  # can check for contradiction
                if last1 != last2
                    # println("query result $qres is contradiction")
                    return false => change
                end
            end
        end
    end
    return true => change
end



function check_limits!(mod::Model, c_data)::Bool
    cset = to_cset(mod)
    for (dia, c_tabs, (_, apex, legs)) in c_data
        println("DIAGRAM $apex $legs - ctabs = $c_tabs")
        npart = nparts(cset, apex)
        for matches in query(cset, dia)
            println("\tmatch $matches")
            if all(i->matches[i] < nparts(cset,c_tabs[i]), 1:length(c_tabs)) # ignore matches with unknowns
                poss_apexes = Set(1:npart)
                for (legval,leg) in zip(matches,legs)
                    if leg != 0
                        leg_edge = es(leg)
                        println("legval $legval with edge_in $leg_edge has preimage $(cset.indices[leg_edge][legval])")
                        intersect!(poss_apexes, cset.indices[leg_edge][legval])
                    end
                end
                has_null, n_apex = npart in poss_apexes, length(poss_apexes)
                if  !(n_apex in (has_null ? [1,2] : [1]))
                    println("\tREJECTING $poss_apexes")
                    return false
                end
            end
        end
    end
    return true
end

function find_models(fls::FLSketch, consts::Vector{Int})#::Vector{Model}
    # INITIALIZE
    schema = fls.G
    res=[]
    seen=Set{UInt64}()
    modl = Model(schema, consts)

    # Initialize commutative diagram data
    c_paths = comm_paths(fls)
    comm_qs = [paths_to_query(schema, p1, p2) for (p1, p2) in c_paths]

    # Initialize cone data
    cone_ds = [diagram_to_query(conedia) for (apex, conedia) in fls.C]
    cone_tabs = [xs(cone[1].components[:V].func) for cone in fls.C]

    function find_models_rec!(mod::Model)
        hsh = hash(mod)
        m = to_cset(mod)
        println("finding models for $(m[:e1]), $(m[:e2])\n\t$(str(mod)) (seen = $(hsh in seen))")
        if !(hsh in seen)
            push!(seen, hsh)
            success, _ = check_diagrams!(mod, zip(comm_qs, c_paths))
            if success
                if is_sat(mod)
                    canon_hsh = canonical_hash(to_cset(mod, true))
                    if !(canon_hsh in seen)
                        push!(res, canon_hsh => deepcopy(mod))
                        println("pushed $(length(res))'th model w/ hash $canon_hsh")
                        push!(seen, canon_hsh)
                    end
                    return
                else
                    choose!(mod)
                end
            end
        end
    end

    """
    Take an FK that is not matched to a PK. Resursively
    explore models that have the FK set to all possible
    values of the PK of the target table OR create a fresh
    PK and map to it.
    """
    function choose!(mod::Model)
        for (e, tgt) in enumerate(mod.tgt)
            tgt_pks = mod.pks[tgt]
            for (src_index, considered) in enumerate(mod.considered[e])
                unconsidered = setdiff(tgt_pks, considered)
                if !isempty(unconsidered)
                    new_mod = deepcopy(mod)
                    new_mod.considered[e][src_index] = Set(tgt_pks)
                    for u in unconsidered
                        newer_mod = deepcopy(new_mod)
                        newer_mod.fks[e][src_index] = u
                        # println("SETTING EDGE $e index $src_index to value $u")
                        find_models_rec!(newer_mod)
                    end
                end

                # THINGS GO HAYWIRE
                if 1+1==1 # size(mod) < MAXSIZE
                    new_mod = deepcopy(mod)
                    new_id = push!(new_mod, tgt)
                    # println("ADDED $new_id to table $tgt of $new_mod")
                    # println(to_cset(new_mod))
                    new_mod.considered[e][src_index] = union(Set(tgt_pks), Set([new_id]))
                    new_mod.fks[e][src_index] = new_id
                    find_models_rec!(new_mod)
                end
            end
        end
    end

    find_models_rec!(modl)
    return res
end

# """
# Brute force try all assignments to see if diagrams are satisfied
# with the number of elements in each set fixed by consts

# Algorithm:

# Algorithm:
# - Start of with CSet initialized to have elements for each const
#   that is known to not be a limit cone,
#   plus one extra value meant to represent unknown (value=1).
# - All values of FKs are initialized to 1.
# - For each 1 we find, branch out a possibility where it takes any possible value.

# - For each possibility, check all diagrams
#   - positive info: fill out things we can derive if one leg is known and other unknown
#   - negative info: find a contradiction, short circuit
# - For each cone, check its base diagram and for each matching set of elements
#   - positive info: if no apex found, create an element in the apex and add it
#                    as a possibility to everything that points to that table
#   - negative info: if two different things are an apex, fail (can this happen?)

# - Repeat this until the entire CSet is defined, then trim off the 'unknown' values.
# """
# function term_models(fls, consts::Tuple)::Vector{CSet}

#     # Initialize model
#     G = fls.G
#     modl = graph_to_cset(G)()

#     # Initialize constants + EXTRA SENTINAL VALUE = "UNKNOWN"
#     for (i, c) in enumerate(consts)
#         add_parts!(modl, xs(i), c+1;)
#     end
#     # initialize foreign keys to unknown value
#     for e in 1:ne(G)
#         n_in, n_out = [nparts(modl, G[x][e]) for x in [:src, :tgt]]
#         set_subparts!(modl, 1:n_in; Dict([es(e)=>n_out])...)
#     end

#     # Initialize commutative diagram data
#     c_paths = comm_paths(fls)
#     comm_qs = [paths_to_query(G, p1, p2) for (p1, p2) in c_paths]
#     comm_q_tabs = [xs(lasttabs(G, p1, p2)) for (p1, p2) in c_paths]

#     # Initialize cone data
#     cone_ds = [diagram_to_query(cone[1]) for cone in fls.C]
#     cone_tabs = [xs(cone[1].components[:V].func) for cone in fls.C]

#     function rec!(cset::CSet, res::Vector{CSet},seen::Set{UInt64})
#         # Fill out any info we can from diagrams, detect contradiction
#         for (comm_q, cqtab, (pth1, pth2)) in zip(comm_qs, comm_q_tabs, c_paths)
#             for qres in query(cset, comm_q)
#                 penult1, penult2, last1, last2 = qres
#                 nullp1, nullp2, null1, null2 = map(
#                     tabval -> tabval[2] == nparts(cset, tabval[1]), zip(cqtab, qres))
#                 if null1 && !null2 && !nullp1 # can propagate info
#                     set_subpart!(cset, penult1, es(pth1[end]), last2)
#                 elseif !null1 && null2 && !nullp2 # can propagate info
#                     set_subpart!(cset, penult2, es(pth2[end]), last1)
#                 elseif !(null1||null2)  # can check for contradiction
#                     if last1 != last2
#                         return
#                     end
#                 end
#             end
#         end

#         for (dia, c_tabs, (_, apex, legs)) in zip(cone_ds, cone_tabs, fls.C)
#             println("DIAGRAM $apex $legs - ctabs = $c_tabs")
#             npart = nparts(cset, apex)
#             for matches in query(cset, dia)
#                 println("\tmatch $matches")
#                 if all(i->matches[i] < nparts(cset,c_tabs[i]), 1:length(c_tabs)) # ignore matches with unknowns
#                     poss_apexes = Set(1:npart)
#                     for (legval,leg) in zip(matches,legs)
#                         if leg != 0
#                             leg_edge = es(leg)
#                             println("legval $legval with edge_in $leg_edge has preimage $(cset.indices[leg_edge][legval])")
#                             intersect!(poss_apexes, cset.indices[leg_edge][legval])
#                         end
#                     end
#                     has_null, n_apex = npart in poss_apexes, length(poss_apexes)
#                     if  !(n_apex in (has_null ? [1,2] : [1]))
#                         println("\tREJECTING $poss_apexes")
#                         return
#                     end
#                 end
#             end
#         end

#         # split cases on an arbitrary choice for the first zero we find
#         for i in shuffle(1:ne(schema))
#             e = es(i)
#             tgt_table = xs(G[:tgt][i])
#             for (j, val) in shuffle(collect(enumerate(cset[e][1:end-1])))
#                 if val == nparts(cset, tgt_table)  #SPLIT
#                     for k in 1:(val-1)
#                         cset2 = deepcopy(cset)
#                         set_subpart!(cset2, j, e, k)
#                         hsh = canonical_hash(cset2)
#                         if !(hsh in seen)
#                             push!(seen,hsh)
#                             rec!(cset2, res, seen)
#                         end
#                     end
#                     return res
#                 end
#             end
#         end
#         # No unknown values! Delete the last value from every table
#         for t in keys(cset.tables)
#             rem_part!(cset, t, nparts(cset, t))
#         end
#         hsh = canonical_hash(cset)
#         if hsh in seen
#             return
#         else
#             push!(seen, hsh)
#             push!(res, cset)
#         end
#     end
#     res, seen = CSet[], Set{UInt64}()
#     rec!(modl, res, seen)
#     return res
# end