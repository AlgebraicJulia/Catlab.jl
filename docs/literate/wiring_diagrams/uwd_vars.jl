using Catlab
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.StructuredCospans
using Catlab.Programs
using Catlab.Graphics
using Catlab.Graphics.Graphviz

draw(uwd::AbstractUWD) = to_graphviz(uwd, junction_labels=:variable, box_labels=:name)


fickslaw = @relation (C,ϕ) begin
    Fick(C, ϕ)
end

draw(fickslaw)

netflux = @relation (u̇, ϕᵤ) begin
    d(ϕᵤ, dϕ)
    ⋆(u̇, dϕ)
end

draw(netflux)

diffuwd = @relation () begin
    Fick(C,ϕ)
    #dₜ(C,Ċ)
    Φ(Ċ,ϕ)
end

draw(diffuwd)

function rename_variables!(uwd, boxes)
    map(1:length(boxes)) do b
        ports = incident(uwd, b, :box)
        jnames = uwd[ports, [:junction, :variable]]
        newnames = map(parts(boxes[b], :OuterPort)) do op
            j = boxes[b][op, :outer_junction]
            oldname = boxes[b][j, :variable]
            # for box $b outer junction $j, renames $oldname → $(jnames[j])
            return jnames[j]
        end
        boxes[b][boxes[b][:outer_junction], :variable] .= newnames
    end
    return boxes
end
ocompose_rename!(uwd, boxes) = ocompose(uwd, rename_variables!(uwd,boxes))

ocompose_rename!(diffuwd, [fickslaw, netflux]) |> draw

adv_diff = @relation (C,u) begin
    Fick(C,ϕ)
    Add(ϕ₊, ϕ, ϕₐ)
    Φ(C,ϕ₊)
    Flow(u, C, ϕₐ)
end

draw(adv_diff)

add = @relation (ϕ₁, ϕ₂, ϕ₊) begin
    +(ϕ₁, ϕ₂, ϕ₊)
end

flow = @relation (u, v, ϕ) begin
    ℒ(v, u, ϕ)
end

ocompose_rename!(adv_diff, [fickslaw, add, netflux, flow]) |> draw

twoflux = @relation (u, ϕ₁, ϕ₂) begin
    dₜ(u, du)
    netflux(du, ϕ₊)
    +(ϕ₁, ϕ₂, ϕ₊)
end
draw(twoflux)

Ċ = @relation (C, du) begin dₜ(C, du) end
tf = ocompose_rename!(twoflux, [Ċ, netflux, add])
draw(tf)

adꜛ = @relation () begin
    twoflux(C, ϕᵈ, ϕᵃ)
    Fick(C, ϕᵈ)
    Flow(u, C, ϕᵃ)
end

draw(adꜛ)

ocompose_rename!(adꜛ, [tf, fickslaw, flow]) |> draw