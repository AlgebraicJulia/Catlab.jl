using Catlab
using Catlab.Doctrines

export crand


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
    dims = cumsum(map(ndims∘dom, f.args))
    map(1:length(f.args)) do i
        if i == 1
            crand(f.args[i], args[1:dims[1]]...)
        else
            crand(f.args[i], args[dims[i-1]+1:dims[i]]...)
        end
    end |> xs->filter(xs) do x # handle the () you get from deletes
        x != ()
    end
end
function crand(f::FreeCartesianCategory.Hom{:braid}, args...)
    y = args[1:ndims(f.args[1])]
    x = args[(ndims(f.args[1])+1):end]
    return (x...,y...)
end

# Diagonal Comonoid
crand(f::FreeCartesianCategory.Hom{:mcopy}, args...) = (args..., args...)
crand(f::FreeCartesianCategory.Hom{:delete}, args...) = ()
