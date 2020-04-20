using Catlab
using Catlab.Doctrines
import Base: length
length(::FreeCartesianCategory.Ob{:generator}) = 1
length(f::FreeCartesianCategory.Ob{:otimes}) = sum(length.(f.args))

# How do you give semantics to a stochastic map? You call it.
function crand(f::FreeCartesianCategory.Hom{:generator}, args...)
    f.args[1](args...)
end

# Compositional structure
crand(f::FreeCartesianCategory.Hom{:id}, args...) = (args)
function crand(f::FreeCartesianCategory.Hom{:compose}, args...)
    if length(f.args) > 2
        return crand(f.args[end], crand(compose(f.args[1:end-1]...), args...)...)
    end
    return crand(f.args[end], crand(f.args[1], args...)...)
end

# Monoidal Structure
function crand(f::FreeCartesianCategory.Hom{:otimes}, args...)
    map(1:length(f.args)) do i
        crand(f.args[i], args[i]...)
    end |> xs->filter(xs) do x # handle the () you get from deletes
        x != ()
    end
end
function crand(f::FreeCartesianCategory.Hom{:braid}, args...)
    y = args[1:length(f.args[1])]
    x = args[(length(f.args[1])+1):end]
    return (x...,y...)
end

# Diagonal Comonoid
crand(f::FreeCartesianCategory.Hom{:mcopy}, args...) = (args..., args...)
crand(f::FreeCartesianCategory.Hom{:delete}, args...) = ()
