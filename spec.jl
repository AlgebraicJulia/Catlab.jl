#
#
#Target examples for aggregation in Catlab
#------------------------------------
"""
Returns an Aggregator 
"""
A = @aggregate WeightedGraph + s t
G::WeightedGraph{Real}
aggregate(G,A) = Dict(:s=> x->+(s^-1(x)...),:t=> x->+(t^{-1}(x)...))
#or, better,
aggregate(G,A) = 
    @migrate WeightedGraph begin
        V => V
        E => E
        W_E => Weight
        W_V => NamedTuple((:s,:t),Tuple{Weight,Weight})
        w_e => weight
        w_v => x -> (:s=+(s^{-1}(x)),:t=+(t^{-1}(x)))
    end
    #or, although this isn't going to work if there are multiple relevant attribute types
    @migrate WeightedGraph begin
        V => V 
        E => E
        W_E => Weight
        W_V => Weight
        w_e => weight
        w_s => (x->+(s^{-1}(x)))
        w_t => (x->+(t^{-1}(x)))
    end

"""
Collapse all parallel edges in a weighted graph
"""
@migration WeightedGraph WeightedGraph begin
    V => V
    E => @join begin
        v₁ :: V 
        v₂ :: V 
        end
    Weight => Weight
    weight => x -> begin
            X = s^-1(v₁)∩t^-1(v₂)
            +(X...)
    end
end
#Harper wants something where the weight of an edge can depend on *all* the vertices.
"""
hmm
"""
@migration WeightedAttrGraph WeightedAttrGraph begin
    V => V 
    E => E
    Attr => Attr
    attr => attr 
    Weight => Weight+codom(buildTree)
    weight => x -> (x != 1 ? weight(x) : buildTree([attr(v) for v in V]...))
end

"""
Product of weighted graphs?
"""
@migration WeightedGraph WeightedGraph begin
    V => @join v₁::V;v₂::V 
    E => @join e₁::E,e₂::E 
    weight => weight(e₁)+weight(e₂)#...Just a different issue, methinks
end









