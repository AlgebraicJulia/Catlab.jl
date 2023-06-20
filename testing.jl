using ACSets, Catlab, Catlab.Graphs, Catlab.Present, 
    Catlab.Programs.DiagrammaticPrograms, Catlab.CategoricalAlgebra.DataMigrations,
    Catlab.CategoricalAlgebra.FinCats


@present SchMechLink <: SchGraph begin
    Pos::AttrType
    Len::AttrType
    pos::Attr(V,Pos)
    len::Attr(E,Len)
end
@acset_type MechLink(SchMechLink, index=[:src,:tgt])
G = @acset MechLink{Vector{Float64},Float64} begin
    V = 3
    E = 2
    src = [1,2]
    tgt = [2,3]
    len = [1.0,1.0]
    pos = [[1.0,1.0,1.0],[2.0,2.0,2.0],[2.0,2.0,1.0]]
end

#Rotate the whole linkage by a bit
A = @migration SchMechLink SchMechLink begin
    V => V
    E => E
    Pos => Pos
    Len => Len
    src => src
    tgt => tgt
    pos => begin 
            θ = π/5
            M = [[cos(θ),-sin(θ),0] [sin(θ),cos(θ),0] [0,0,1]]
            x -> M*pos(x)
            end
    len => len
end
migrate(G,A)

#Filter impossible edges out of a mechanical linkage
M = @migration SchMechLink SchMechLink begin
    V => V
    E => @join begin
            e :: E
            L :: Len
            (l:e→L) :: (x->len(x)^2)
            (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
        end
    Pos => Pos
    Len => Len
    src => src(e)
    tgt => tgt(e)
    pos => pos
    len => len(e)
end

#Filter impossible edges out of a mechanical linkage while rotating
M = @migration SchMechLink SchMechLink begin
    V => V
    E => @join begin
            e :: E
            L :: Len
            (l:e→L) :: (x->len(x)^2)
            (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
        end
    Pos => Pos
    Len => Len
    src => src(e)
    tgt => tgt(e)
    pos => begin 
            θ = π/5
            M = [[cos(θ),-sin(θ),0] [sin(θ),cos(θ),0] [0,0,1]]
            x -> M*pos(x)
            end
    len => len(e)
end


Mm = @migration SchMechLink begin
    V => V
    E => @join begin
            e :: E
            L :: Len
            (l:e→L) :: (x->len(x)^2)
            (d:e→L) :: (x->sum((pos(src(x))-pos(tgt(x))).^2))
        end
    Pos => Pos
    Len => Len
    (src:E→V) => src(e)
    (tgt:E→V) => tgt(e)
    (pos:V→Pos) => pos
    (len:E→Len) => len(e)
end


Aa = @migration SchMechLink begin
    V => V
    E => E
    Pos => Pos
    Len => Len
    (src:V→E) => src
    (tgt:V→E) => tgt
    (pos:V→Pos) => begin 
            θ = π/5
            M = [[cos(θ),-sin(θ),0],[sin(θ),cos(θ),0],[0,0,1]]
            x -> M*pos(x)
            end
    (len:E→Len) => len
end

#=
@present SchBoxSpring <: SchGraph begin
    Stretch::AttrType
    W::Ob#vertices that are walls
    ι::Hom(W,V)

end


body = :($(Expr(:copyast, :($(QuoteNode(quote
#= REPL[41]:2 =#
V => V
#= REPL[41]:3 =#
E => #= REPL[41]:3 =# @join(begin
            #= REPL[41]:4 =#
            e::E
            #= REPL[41]:5 =#
            L::Len
            #= REPL[41]:6 =#
            (l:e → L)::(x->begin
                        #= REPL[41]:6 =#
                        len(x) ^ 2
                    end)
            #= REPL[41]:7 =#
            (d:e → L)::(x->begin
                        #= REPL[41]:7 =#
                        sum((pos(src(x)) - pos(tgt(x))) .^ 2)
                    end)
        end)
#= REPL[41]:9 =#
Pos => Pos
#= REPL[41]:10 =#
Len => Len
#= REPL[41]:11 =#
src => src(e)
#= REPL[41]:12 =#
tgt => tgt(e)
#= REPL[41]:13 =#
pos => pos
#= REPL[41]:14 =#
len => len(e)
end))))))

C = FinCat(SchWeightedGraph)
mig2 = dp.reparse_arrows(mig).args[2]
mig3 = dp.parse_diagram_ast(mig2)
mig4 = dp.parse_query_diagram(C,mig3)
data = mig4.ob_map[1]
get_ob_type(C::FinCat{Ob,Hom}) where {Ob,Hom} = Ob
get_dd_type(data::dp.DiagramData{T}) where T = T
F_ob, F_hom, J = data.ob_map, data.hom_map, dp.shape(data)
F_ob = dp.mapvals(x -> dp.make_query(C, x), F_ob)
query_type = mapreduce(typeof, dp.promote_query_type, values(F_ob), init=get_ob_type(C))
F_ob = dp.mapvals(x -> dp.convert_query(C, query_type, x), F_ob)
F_hom = dp.mapvals(F_hom, keys=true) do h, f
    dp.make_query_hom(C, f, F_ob[dom(J,h)], F_ob[codom(J,h)])
  end
T = get_dd_type(data)
new_data = dp.DiagramData{T}(F_ob,F_hom,J,data.params)
dp.Diagram(new_data,C)