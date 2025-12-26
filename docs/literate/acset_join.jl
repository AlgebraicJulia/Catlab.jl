using ACSets
using Catlab
using Catlab.Graphs

@present SchTable(FreeSchema) begin
    Name::AttrType
    Column::Ob
    colname::Attr(Column, Name)
end
@acset_type Table(SchTable)

j = Table{Symbol}()
add_part!(j, :Column, colname=:color)
add_part!(j, :Column, colname=:flavor)

k = Table{Symbol}()
add_part!(k, :Column, colname=:mood)

l = Table{Symbol}()
add_part!(l, :Column, colname=:review)
add_part!(l, :Column, colname=:stars)

@present SchEdgeLabeledGraph <: SchLabeledGraph begin
    TableName::AttrType
    tablename::Attr(V, TableName)
    EdgeLabel::AttrType
    edgelabel::Attr(E, EdgeLabel)
    # edgename
end
@acset_type EdgeLabeledGraph(SchEdgeLabeledGraph)

n = EdgeLabeledGraph{Table{Symbol}, Symbol, Pair{Symbol, Symbol}}()
add_part!(n, :V, label=j, tablename=:Tastes)
add_part!(n, :V, label=k, tablename=:Feelings)
add_part!(n, :V, label=l, tablename=:Review)
add_part!(n, :E, src=1, tgt=2, edgelabel=:Tastes => :Feelings)
add_part!(n, :E, src=2, tgt=3, edgelabel=:Feelings => :Review)

function split(sch::BasicSchema)
    splayed = EdgeLabeledGraph{Table{Symbol}, Symbol, Pair{Symbol, Symbol}}()
    tables = map(objects(sch)) do ob
        obtable = Table{Symbol}()
        cols = getindex.(filter(x -> x[2] == ob, attrs(sch)), 2)
        add_parts!(obtable, :Column, length(cols), colname=cols)
        ob => obtable
    end
    foreach(tables) do (name, table)
        add_part!(splayed, :V, label=table, tablename=name)
    end
    foreach(homs(sch)) do (f, src, tgt)
        s = incident(splayed, src, :tablename)
        t = incident(splayed, tgt, :tablename)
        add_part!(splayed, :E, src=only(s), tgt=only(t), 
                  edgelabel=src => tgt)
    end
    splayed
end    

# stitch this together
# 1. break tablename into Obs
# 2. labels becomes columns (attrs)
# 3. edges become homs

""" Sends the graph internal to ACSets into an ACSet schema""" 
function Base.join(g::EdgeLabeledGraph)
    obs = Symbol[]
    attrs = Tuple{Symbol, Symbol, Symbol}[]
    homs = Tuple{Symbol, Symbol, Symbol}[]
    foreach(parts(g, :V)) do id
        table = subpart(g, id, :tablename)
        push!(obs, table)
        attributes = subpart(subpart(g, id, :label), :colname)
        # TODO AttrType
        push!(attrs, [(a, table, :Name) for a in attributes]...)
    end
    foreach(parts(g, :E)) do id
        src = subpart(g, id, :src)
        tgt = subpart(g, id, :tgt)
        el = subpart(g, id, :edgelabel) # :flavor => :color
        push!(homs, (Symbol("$(el.first)$(el.second)"), el.first, el.second))
    end
    BasicSchema(obs, homs, Symbol[:Name], attrs)
end

# join(split(sch))

SchAnew = join(n)

@acset_type New(SchAnew, index=[:TasteFeelings])
