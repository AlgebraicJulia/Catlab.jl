module Category
export dom,codom,id,compose,otimes,munit,∘,⊗

# TODO
#
# https://github.com/jasonmorton/Typeclass.jl
# https://github.com/mauro3/Traits.jl#other-trait-implementations
abstract Obj
abstract Mor

# Category
##########
dom(f::Mor)::Obj = nothing
codom(f::Mor)::Obj = nothing
id(A::Obj)::Mor = nothing
compose(f::Mor, g::Mor)::Mor = nothing

# Unicode syntax
∘(f,g) = compose(f,g)

# Monoidal category
###################
otimes(f::Mor, g::Mor)::Mor = nothing
otimes(A::Obj, B::Obj)::Obj = nothing
munit()::Obj = nothing

# Unicode syntax
⊗(f::Mor, g::Mor)::Mor = otimes(f, g)
⊗(A::Obj, B::Obj)::Obj = otimes(A, B)

end
