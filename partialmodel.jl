include("sketchgat.jl");


####################
# Helper functions #
####################

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
#######################
# Main data structure #
#######################
"""
Everything we know about a partial-information model

Because items can be added to the target in the future,
we must record which values we have considered.
"""

struct Model
    tables::Vector{IntDisjointSets}
    fks::Vector{Vector{Int}}
    pks::Vector{Vector{Int}} # which id's are primary
    considered::Vector{Vector{Set{Int}}} # which alternative vals we've already split this FK on
    #cones::Vector{Dict{Int,Vector{Int}}} # all vals should be unique in dict
end

function validate_model(fls::FLSketch, m::Model)::Nothing
    n = length(m.tbls)
    # number of fks matches up with src/tgt
    @assert length(fks) == length(src) == length(tgt)

    # src/tgt refer to nodes
    @assert all(v->0 < v <= n, vcat(src,tgt))

    # num of vals in fk[e] equals num of vals in pk[src[e]]
    @assert all([length(fkvect) == length(pks[src[e]])
                 for (e, fkvect) in enumerate(fks)])

    # every equiv class is referred to by some PK or an FK
    # every index in fks/pks/considered refers to something
    # every cone dictionary has unique values
    # each cone value has the right number of legs
    #
end



"""
Initialize model from FLS data.

# of constants is specified for each NON CONE table
cone tables are initialized to an apex for each possibility.
"""
function Model(fls::FLSketch, consts::Vector{Int})::Model
    n   = nparts(fls.G, :V)
    src = fls.G[:src]
    tgt = fls.G[:tgt]

    pks = [collect(1:i) for i in consts]
    fks = [Vector{Int}() for _ in 1:length(src)]

    tabls = []
    for tab in 1:n
        counter = length(pks[tab])
        incident_edges = fls.G.indices[:tgt][tab]
        for e in incident_edges
            for _ in 1:length(pks[src[e]])
                counter+=1
                push!(fks[e], counter)
            end
        end
        push!(tabls, IntDisjointSets(counter))
    end

    considered = [[Set{Int}() for _ in 1:length(pks[s])] for s in src]

    return Model(tabls, fks, pks, considered)
end


######################
# COMBINATORIAL REPR #
######################
@present TheoryModel(FreeSchema) begin
  (Elem, PK,  HomElem, Considered)::Ob
  Ind::Data
  obj::Attr(Elem, Ind)
  hom::Attr(HomElem, Ind)

  pe::Hom(PK, Elem)
  hesrc::Hom(HomElem, PK)
  hetgt::Hom(HomElem, Elem)
  che::Hom(Considered, HomElem)
  cpk::Hom(Considered, PK)
end

const CombModel = ACSetType(TheoryModel, index=[
    :obj,:hom,:pe,:hesrc,:hetgt,:che,:cpk]){Int};

#################
# BASIC METHODS #
#################

function Base.length(m::Model)::Int
    return length(m.tables)
end

function size(mod::Model)::Int
    return sum(map(length,mod.pks))
end

function Base.hash(mod::Model, fls::FLSketch)::UInt64
    m = to_combinatorial(mod, fls)
    return canonical_hash(m)
end

"""
Add an element to a table. Other tables' "considered" is now
missing an element.
"""
function Base.push!(modl::Model, G::CSet, tab::Int)::Int
    # Add a new item in the target table and link to PK
    newval = push!(modl.tables[tab])
    push!(modl.pks[tab], newval)
    # For each table tab points to, add a new element for the FK val
    for arr in G.indices[:src][tab]
        tgt = G[:tgt][arr]
        fkval = push!(modl.tables[tgt])
        push!(modl.fks[arr], fkval)
    end
    return newval
end

function Base.show(io::IO, ::MIME"text/plain",mod::Model)
    show(io, "Mod($([t.parents for t in mod.tables]), fk=$([fk for fk in mod.fks]), pk=$([pk for pk in mod.pks]))")
end

function str(m::Model)::String
    io = IOBuffer();
    show(IOContext(io, :limit => true, :displaysize => (20, 40)), "text/plain", m);
    return  String(take!(io));
end


########################################
# CONVERSION TO/FROM DIFFERENT FORMATS #
########################################

"""
Loses the considered and cone information, but organizes the
data in a way amenable to conjunctive queries / visualization

If sat, then we assume all FKs are matched, so we do
not need to create an extra "unknown" value per table

There will be 0 values in the result CSet if `sat` is
set to true when it oughtn't be
"""
function to_cset(m::Model, G::CSet, sat::Bool=false)::CSet
    res = graph_to_cset(G)()
    for (tab, pks) in enumerate(m.pks)
        add_parts!(res, xs(tab), length(pks)+(sat ? 0 : 1))
    end
    for (arr, fks) in enumerate(m.fks)
        tgt_tab = G[:tgt][arr]
        vals = [get_pk(m, tgt_tab, fkval) - (sat ? 1 : 0) for fkval in fks]
        set_subpart!(res, es(arr), vcat(sat ? Int[] : [1], vals))
    end
    return res
end

"""
Create a model with no identities between FKs not matched
to a PK and no `cone` or `considered` information
"""
function from_cset(cset::ACSet{CD}, sat::Bool=true)::Model where {CD}
    n, arrs, src, tgt = length(ob(CD)), hom(CD), collect(dom(CD)), collect(codom(CD))
    G = Graph(n)
    add_edges!(G, src, tgt)

    pks = [collect(1:nparts(cset, i) - (sat ? 0 : 1)) for i in 1:n]
    fks = [Vector{Int}() for _ in 1:length(src)]

    tabls = []
    for tab in 1:n
        counter = length(pks[tab])
        incident_edges = G.indices[:tgt][tab]
        for e in incident_edges
            arr = arrs[e]
            for (src_id, fkval) in enumerate(cset[arr][(sat ? 1 : 2):end])
                if !sat && fkval == 1 # UNKNOWN
                    counter+=1
                    push!(fks[e], counter)
                else
                    push!(fks[e], fkval - (sat ? 0 : 1))
                end
            end
        end
        push!(tabls, IntDisjointSets(counter))
    end

    considered = [[Set{Int}() for _ in 1:length(pks[s])] for s in src]
    return Model(tabls,fks,pks,considered)
end

"""Encode Model as a CSet"""
function to_combinatorial(mod::Model, fls::FLSketch)::ACSet
    G = fls.G
    res = CombModel()
    srcarrs = G.indices[:src]
    pkdata = Dict{Int,Tuple{Int,Int,Int,Dict{Int,Int}}}[]
    fkdata = Dict{Tuple{Int,Int,Int}, Int}() # (tab, pk, fk) => homelem

    for tab in 1:length(mod)
        pk_unique = Dict()
        for (i, pk) in enumerate(mod.pks[tab])
            pk_id = mod.tables[tab].parents[pk]
            if !haskey(pk_unique, pk_id)
                cset_pk_id = add_part!(res, :PK)
                cset_pk_elem_id = add_part!(res, :Elem)
                # set_subpart!(res, cset_pk_id, :po, tab)
                set_subpart!(res, cset_pk_elem_id, :obj, tab)
                set_subpart!(res, cset_pk_id, :pe, cset_pk_elem_id)

                fks = Dict{Int,Int}()
                for arr in srcarrs[tab]
                    fks[arr] = add_part!(res, :HomElem)
                    set_subpart!(res, fks[arr], :hom, arr)
                    set_subpart!(res, fks[arr], :hesrc, cset_pk_id)
                    fkdata[(tab, i,arr)] = fks[arr]
                end
                pk_unique[pk_id] = (i, cset_pk_id, cset_pk_elem_id, fks)
            end
        end
        push!(pkdata, pk_unique)
    end
    for (tab, pkdatas) in enumerate(pkdata)
        for (_, (orig_index,_,_,fks)) in collect(pkdatas)
            for arr in srcarrs[tab]
                tgt = G[:tgt][arr]
                homelem = fks[arr]
                raw_fk = mod.fks[arr][orig_index]
                tgt_class = mod.tables[tgt].parents[raw_fk]
                if haskey(pkdata[tgt],tgt_class)
                    tgt_elem_id = pkdata[tgt][tgt_class][3]
                else
                    tgt_elem_id = add_part!(res, :Elem)
                    set_subpart!(res, tgt_elem_id, :obj, tgt)
                end
                set_subpart!(res, homelem, :hetgt, tgt_elem_id)
            end
        end
    end

    # Considered
    for (fk, considereds) in enumerate(mod.considered)
        source, target = G[:src][fk], G[:tgt][fk]
        for (pk_index, considered) in enumerate(considereds)
            pk_index = mod.tables[source].parents[pk_index]
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
    # Cones

    # for ((apex,coneM), (apex, legs)) in zip(fls.C,collect(mod.cones))
    #     con_id = add_part!(res, :Cone)
    #     apextab = coneM[:V](apex)
    #     set_subpart!(res, con_id, :cone, cone_ind)
    #     set_subpart!(res, _, :apex, _)
    #     for (leg_ind, leg) in enumerate(legs)
    #         leg_id = add_part!(res, :Leg)
    #         set_subpart!(res, leg_id, :leg, leg_ind)
    #         set_subpart!(res, leg_id, :legcone, con_id)

    #         # find which fk leg corresponds to
    #         legfk = fkdata[(legtab, leg, cone[:E](leg_arr))]
    #         set_subpart!(res, leg_id, :legelem, legfk)
    #     end
    # end
    return res
end


"""
Parse a CSet. This is not a strict inverse to to_combinatorial
but the pair forms an involution. `from` will discard elements
in the union-find that are not referred to by any PK or FK,
thereby collapsing things known to be equal.
"""
function from_combinatorial(mod::ACSet, fls::FLSketch)::Model
    G = fls.G
    # Elem offset allows us to number the elements in Elem
    # table. We partition it into contiguous regions so that
    # 1-n, n+1-m, etc. correspond to different tables
    elem_offset, tables, pks, fks, cons = [0], [], [], [], []
    for x in mod.indices[:eo]
        push!(tables, IntDisjointSets(length(x)))
        push!(elem_offset, elem_offset[end]+length(x))
    end
    for tab in 1:length(tables)
        pkelems = [i for i in mod.indices[:obj][tab] if !isempty(mod.indices[:pe][i])]
        push!(pks, [pk-elem_offset[tab] for pk in pkelems]) #mod.indices[:po][tab]])
    end
    for (fk_id, (srctab, tgttab)) in enumerate(zip(src, tgt))
        homelems = Set(mod.indices[:hom][fk_id])
        fk_vect, con_vect = [], []

        for pk in pks[srctab]
            hes = filter(x->x in homelems, mod.indices[:hesrc][pk])
            @assert length(hes) == 1
            he = hes[1]
            push!(fk_vect, mod[:hetgt][he]-elem_offset[tgttab])
            consids = mod[:cpk][mod.indices[:che][he]]
            push!(con_vect, Set([c - elem_offset[tgttab] for c in consids]))
        end
        push!(fks, fk_vect)
        push!(cons, con_vect)
    end
    cones = [] # TODO
    return Model(src, tgt, tables, fks, pks, cons, cones)
end


########
# MISC #
########
"""
Check whether there are any unknown values
If inactive cones refer to unknown values, that is ok
If anything active refers to an inactive cone, that is not ok
"""
function is_sat(mod::Model, fls::FLSketch)::Bool
    for (edge, fk_vect) in enumerate(mod.fks)
        srctab, tab = fls.G[:src][edge], fls.G[:tgt][edge]
        for fk_elem in fk_vect
            if !any(
                map(pk->in_same_set(mod.tables[tab], pk, fk_elem),
                    mod.pks[tab]))
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

"""
Union two elements of table `tab`

"""
function union_fk!(mod::Model, tab::Int, fk1::Int, val1::Int, fk2::Int, val2::Int)::Nothing
    # println("Forcing mod $mod\ntgt x$tab: e$fk1 #$val1 = e$fk2 $val2")
    v1 = mod.fks[fk1][val1]
    if fk2 == 0
        v2 = mod.pks[tab][val2]
    else
        v2= mod.fks[fk2][val2]
    end
    union!(mod.tables[tab], v1, v2)
    return nothing
end

# """
# Ordering of the tables such that, if A is a limit that depends
# on B, that A appears before B. Also return the underlying
# dependency graph.
# """
# function limit_order(f::FLSketch)::Tuple{ACSet,Vector{Int},Dict{Int,Int}}
#     n = nparts(f.G, :V)
#     dag = Graph(n)
#     edict = Dict{Int,Int}()
#     for (apex, conediagram) in f.C
#         apextab = conediagram[:V](apex)
#         for e in dom(conediagram).indices[:src][apex]
#             original_e = conediagram[:E](e)
#             tgt = f.G[:tgt][original_e]
#             if tgt != apextab
#                 e = add_edge!(dag, apextab,tgt)
#                 edict[e] = original_e
#             end
#         end
#     end
#     ord = reverse(topological_sort(dag))
#     return (dag, ord, edict)
# end

# """Assume we are given a cardinality for each (and only)
# non limit object (exception: limits which refer to themselves).
# We compute the maximum cardinality of each object.

# Returns:
#  - the cardinality of each table
#  - the values of each cone arrow
# """
# function get_nums(f::FLSketch, consts::Dict{Int,Int})::Tuple{Vector{Int}, Dict{Int, Vector{Int}}}
#     dag, ord, edict = limit_order(f)
#     res = repeat([0], length(ord))
#     for tab in ord
#         if haskey(consts, tab)
#             res[tab] = consts[tab]
#         else
#             legs = dag.indices[:src][tab]
#             tgts = dag[:tgt][legs]
#             res[tab] = 1
#             for t in tgts
#                 res[tab] *= res[t]
#             end
#         end
#     end
#     eres = Dict{Int, Vector{Int}}()
#     for arrs in filter(!isempty, dag.indices[:src])
#         combos = reduce(vcat,collect(prod([1:res[dag[:tgt][e]] for e in arrs]...)))
#         #println("COMBOS $combos \n\tarrs $arrs")
#         for (i, arr) in enumerate(arrs)
#             eres[edict[arr]] = [tup[i] for tup in (combos isa Tuple ? [combos] : combos)]
#         end
#         #println("PROCESSING arrs $([es(edict[x]) for x in arrs])\n$combos")
#     end
#     return res, eres
# end
