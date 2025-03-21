"""
`force` behaves differently when the domain is finite because we can compute 
a normal form. This should really be called "normalize". It coerces the 
function to a `FinFnVector` (if dom is `FinSetInt`) or `FinFnDict` (otherwise).
"""
module Cast 

export coerce_findom

using GATlab: getvalue

using ..BasicSets: FinSetInt, FinSetHash, ProdSet, FinSet, SetFunction, 
  FinDomFunction, FinSetAsSet, dom, codom


function coerce_findom(s::SetFunction)
  d = getvalue(dom(s))
  if d isa FinSetAsSet
    d = getvalue(getvalue(d))
    if d isa FinSetInt 
      return FinDomFunction([s(i) for i in d], codom(s))
    elseif d isa FinSetHash 
      return FinDomFunction(Dict(k=>s(k) for k in getvalue(d)), FinSet(d), codom(s))  
    end
  elseif d isa ProdSet && all(x->getvalue(x) isa FinSetAsSet, d)
    new_dom = FinSet(dom(s))
    return FinDomFunction(Dict(k=>s(k) for k in new_dom), new_dom, codom(s))
  end

  error("Cannot coerce $s to a `FinDomFunction`: \ndomain $d :: $(typeof(d))")
end


end # module
