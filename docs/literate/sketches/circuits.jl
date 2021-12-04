# # Circuits form a Cartesian Category
# A classic example of a category of computations that is studied by electrical engineers and computer scientists is the category of boolean vectors and circuits. The objects in this category are spaces of bit vectors ℤⁿ and the morphisms are binary circuits built out of gates such as AND, OR, NOT gates. The functional completeness theorem of digital logic that every boolean circuit can be expressed entirely in NAND gates and copying.
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using Catlab.Theories
using Catlab.Syntax
using Catlab.GAT
using Catlab.Present
using Catlab.Programs
using Catlab.Graphics
import Catlab.Graphics: Graphviz
import Catlab.Theories: dom, codom, id, compose, otimes, braid, munit, mcopy, delete, pair, proj1, proj2, ⊗, ⋅, σ
show_diagram(d::WiringDiagram) = to_graphviz(d,
    orientation=LeftToRight,
    labels=false, label_attr=:xlabel,
    node_attrs=Graphviz.Attributes(
        :fontname => "Courier",
    ),
    edge_attrs=Graphviz.Attributes(
        :fontname => "Courier",
    )
)

# ## Syntactic representation of logic circuits
# We start with a presentation of our circuit building blocks as follows. We will be working with the NOT, AND, and OR as our building blocks. As an exercise, start with a presentation including only B::Ob and NAND::Hom(B⊗B, B) and define AND, OR and NOT in terms of that presentation.
@present Circuits(FreeCartesianCategory) begin
    B::Ob
    NOT::Hom(B,B)
    AND::Hom(B⊗B,B)
    OR::Hom(B⊗B,B)
    XOR::Hom(B⊗B,B)
end

# We can access our generators via their names. The presentation serves as a namespace that you index with symbols.
B, NOT, AND, OR = Circuits[:B], Circuits[:NOT], Circuits[:AND], Circuits[:OR]

# Our objects are n-dimensional bool spaces which are the input/output types of logic circuits. Digital logic circuits are compatible for composition if and only if they have the right number of input and output pins.
struct CircuitDom
    n::Int
end

# To execute a circuit, we will store its implementation as a function from Vector{Bool} to Vector{Bool}.
struct Circuit
    dom::CircuitDom
    codom::CircuitDom
    impl::Function # Vector{Bool} of size dom -> Vector{Bool} of size codom
end

# It will be handy to implictly convert integer values to CircuitDom values with this convenience constructor.
Circuit(nins::Int, nouts::Int, impl) = Circuit(CircuitDom(nins), CircuitDom(nouts), impl)

# You can apply a circuit to a specified input vector by calling its implementation function on that input.
apply(circuit::Circuit, input::Vector{Bool})::Vector{Bool} = circuit.impl(input)

# Our basic logic gate implementations
iNOT = Circuit(1, 1, x->!(x[1]))

iAND = Circuit(2, 1, x->[x[1] && x[2]])

iOR = Circuit(2, 1, x->[x[1] || x[2]])

# Make circuits compositional by implementing them as an SMC instance
# Some important points are:
# 1. Circuit composition is function composition.
# 2. The Monoidal product of circuits runs both circuits and concatenates the results.
# 3. The symmetric braiding just swaps the A and B parts of the input vector.
# 4. Our Monoidal unit is a 0-dimensional bool space (i.e. a point or empty list).
# 5. Circuits are Cartesian because we can copy data and delete by projection.
#
# The fact that circuit composition is function composition is based on the forgetful functory from the category of circuits into the category Set. This functor is what makes Circuit a concrete category, that is a category whose objects are sets and whose morphisms are determined by functions on those sets.
@instance CartesianCategory{CircuitDom, Circuit} begin
    id(A::CircuitDom) = Circuit(A,A, x->x)
    dom(f::Circuit) = f.dom
    codom(f::Circuit) = f.codom

    compose(f::Circuit, g::Circuit) = begin
        @assert(f.codom == g.dom)
        return Circuit(f.dom, g.codom, x->g.impl(f.impl(x)))
    end

    otimes(A::CircuitDom, B::CircuitDom) = CircuitDom(A.n + B.n)
    otimes(f::Circuit, g::Circuit) = begin
        impl = x -> vcat(f.impl(x[1:f.dom.n]), g.impl(x[f.dom.n + 1:end]))
        return Circuit(f.dom.n + g.dom.n, f.codom.n + g.codom.n, impl)
    end

    braid(A::CircuitDom, B::CircuitDom) = begin
        impl = x -> vcat(x[A.n+1:end], x[1:A.n])
        n = A.n + B.n
        Circuit(n, n, impl)
    end

    munit(::Type{CircuitDom}) = CircuitDom(0)

   mcopy(A::CircuitDom) = Circuit(A.n, A.n+A.n, x->vcat(x,x))
    delete(A::CircuitDom) = Circuit(A.n, 0, x->Bool[])

    pair(f::Circuit, g::Circuit) = begin
        @assert(f.dom == g.dom)
        return Circuit(f.dom.n, f.codom.n+g.codom.n, x->vcat(f.impl(x), g.impl(x)))
    end
    proj1(A::CircuitDom, B::CircuitDom) = Circuit(A.n+B.n, A.n, x->x[1:A.n])
    proj2(A::CircuitDom, B::CircuitDom) = Circuit(A.n+B.n, B.n, x->x[A.n+1:end])
end

# Catlab provides the function `functor` to construct a functor from circuit diagrams to circuit implementations.
gens = Dict(B=>CircuitDom(1), NOT=>iNOT, AND=>iAND, OR=>iOR)
Impl(expr) = functor((CircuitDom, Circuit), expr, generators=gens)

# With this in place we can make some circuits.
XOR = @program Circuits (x::B, y::B) begin
    xnandy = NOT(AND(x,y))
    xory = OR(x,y)
    return AND(xnandy,xory)
end
show_diagram(XOR)

# Then we can use the functor to construct our circuit from the syntax description along with the implementations of the building blocks.
XOR_expr = to_hom_expr(FreeCartesianCategory, XOR)
iXOR = Impl(XOR_expr)
@time apply(iXOR, [true, false])

# ## The Operadic View
# For any SMC, there is an operad of wiring diagrams given by substitution of boxes with diagrams that have the same signature. Often, when you do the mathematical work of applying category theory to a new scientific or engineering domain, it is convenient to work in some doctrine of category theory such as SMCs or Hypergraph Categories. However, when you do the computational work of applying the algorithms, you should pass to the operadic view to get more efficient computations. Notice that the XOR circuit defined above creates several intermediate functions to execute the circuit. This was easy for us to define directly from the mathematical description of how circuits work, but makes the Julia compiler do a lot of work to execute the circuit because each term constructor in our hom expression results in an internal function that Julia must compile.
#
# To avoid this problem, we can implement our apply function as acting directly on a wiring diagram. This will require more thinking about algorithms, but will result in a more efficient implementation.
function apply(prog::WiringDiagram, ops::Dict{Symbol,Circuit}, inputs::Vector{Bool})
  d = prog.diagram
  @assert length(inputs) == nparts(d, :OuterInPort)
  invals = zeros(Bool, nparts(d, :InPort))
  outvals = zeros(Bool, nparts(d, :OutPort))
  outputs = zeros(Bool, nparts(d, :OuterOutPort))
  for iw in parts(d, :InWire)   # initialize input ports with the arguments to the function
    v = inputs[d[iw, :in_src]]
    invals[d[iw, :in_tgt]] = v
  end
  for b in topological_sort(prog) # for each gate, compute the result and write it to your output ports
    opcode = d[b, :value]
    inslots = incident(d, b, :in_port_box)
    args = invals[inslots]
    rets = apply(ops[opcode], args)
    outslots = incident(d, b, :out_port_box)
    outvals[outslots] .= rets
    for w in incident(d, b, [:out_port_box, :src]) # synchronize via the wires
        invals[d[w, :tgt]] = outvals[d[w, :src]]
    end
  end
  for ow in parts(d, :OutWire) # read out the final state
    outputs[d[ow, :out_tgt]] = outvals[d[ow, :out_src]]
  end
  return outputs
end

apply(XOR, GENERATORS, [false, true])

GENERATORS = Dict(:NOT=>iNOT, :AND=>iAND, :OR=>iOR)

for x in Iterators.product([true, false], [true, false])
    y = apply(XOR, GENERATORS, collect(x))
    println("$(x[1])\t$(x[2])\t|  $(y[1])")
end

# So you can see two ways of encoding an instance of an SMC into Catlab. The `@instance` macro lets you directly encode the category theoretic formulation. And the operadic view works with WiringDiagrams directly for more efficient implementations.