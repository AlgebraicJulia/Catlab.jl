module PACSets

export @pacset_type, @abstract_pacset_type, StructPACSet

using MLStyle
using StaticArrays
using Reexport

using ...Present
@reexport using ...ACSetInterface
using ...Theories: MSchemaDesc, MSchemaDescType, MSchemaDescTypeType, MonoidalSchema
@reexport using ...Theories: FreeMonoidalSchema
using ...CSetDataStructures: pi_type, pi_type_elt, q

abstract type StructPACSet{S<:MSchemaDescType, Ts<:Tuple} end

function product_hom_type(s::MSchemaDesc, f::Symbol)
  component_ty = :(Array{Int64, $(length(s.doms[f]))})
  :(Tuple{$(fill(component_ty, length(s.codoms[f]))...)})
end

function product_attr_type(s::MSchemaDesc, f::Symbol)
  component_tys = [:(Array{$T, $(length(s.doms[f]))}) for T in s.codoms[f]]
  :(Tuple{$(component_tys...)})
end

function array_initializer(s::MSchemaDesc, f::Symbol; attr=false, sizes=false)
  type = attr ? x -> x : _ -> :Int64
  size = sizes ? x -> x : _ -> 0
  Expr(:tuple,
       [:(Array{$(type(y)), $(length(s.doms[f]))}(
         undef, $(Expr(:tuple, [size(x) for x in s.doms[f]]...))))
       for y in s.codoms[f]]...)
end
  
function struct_pacset(name::Symbol, parent, p::Presentation{MonoidalSchema})
  s = MSchemaDesc(p)
  parameterized_type, new_call = if length(s.attrtypes) > 0
    (:($name{$(s.attrtypes...)}), :(new{$(s.attrtypes...)}))
  else
    (name, :new)
  end
  schema_type = MSchemaDescTypeType(s)
  obs_t = :($(GlobalRef(StaticArrays, :MVector)){$(length(s.obs)), Int})
  quote
    struct $parameterized_type <: $parent{$schema_type, Tuple{$(s.attrtypes...)}}
      obs::$obs_t
      homs::$(pi_type(s.homs, f -> product_hom_type(s, f)))
      attrs::$(pi_type(s.attrs, f -> product_attr_type(s, f)))
      function $parameterized_type() where {$(s.attrtypes...)}
        $new_call(
          $obs_t(zeros(Int, $(length(s.obs)))),
          $(pi_type_elt(s.homs, f -> array_initializer(s, f))),
          $(pi_type_elt(s.attrs, f -> array_initializer(s, f; attr=true)))
        )
      end

      function $parameterized_type(
        ;$([Expr(:kw, x, 0) for x in s.obs]...),
        $([Expr(:kw, f, nothing) for f in s.homs]...),
        $([Expr(:kw, a, nothing) for a in s.attrs]...)) where {$(s.attrtypes...)}
        $(Expr(:block,
               (map(vcat(s.homs, s.attrs)) do a
                 quote
                   if $a != nothing
                     $(Expr(:block,
                            (map(enumerate(s.doms[a])) do (i,x)
                              quote
                                if $x != 0
                                  @assert $x == size($a)[$i]
                                else
                                  $x = size($a)[$i]
                                end
                              end
                             end)...))
                   end
                 end
                end)...))
        pacs = $new_call(
          $obs_t($(Expr(:vect, s.obs...))),
          $(pi_type_elt(s.homs, f -> array_initializer(s, f; sizes = true))),
          $(pi_type_elt(s.attrs, f -> array_initializer(s, f; sizes = true, attr=true)))
        )
        $(Expr(:block,
               [:($(GlobalRef(ACSetInterface, :set_subpart!))(pacs, $(q(f)), $f))
                for f in vcat(s.homs, s.attrs)]...))
        pacs
      end
    end
  end
end

macro pacset_type(head)
  head, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(PACSets, :StructPACSet))
  end
  name, schema, idx_args = @match head begin
    Expr(:call, name, schema, idx_args...) => (name, schema, idx_args)
    _ => error("Unsupported head for @pacset_type")
  end

  quote
    const tmp = $(esc(:eval))($(GlobalRef(PACSets, :struct_pacset))(
      $(Expr(:quote, name)), $(Expr(:quote, parent)), $(esc(schema))
    ))
  end
end

ACSetInterface.nparts(pacs::StructPACSet, x::Symbol) = _nparts(pacs, Val{x})

@generated function _nparts(pacs::StructPACSet{S}, ::Type{Val{x}}) where {S,x}
  s = MSchemaDesc(S)
  :(pacs.obs[$(findfirst(s.obs .== x))])
end

ACSetInterface.subpart(pacs::StructPACSet, f::Symbol) = _subpart(pacs, Val{f})

@generated function _subpart(pacs::StructPACSet{S}, ::Type{Val{f}}) where {S, f}
  s = MSchemaDesc(S)
  if f ∈ s.homs
    :(pacs.homs.$f[1])
  elseif f ∈ s.attrs
    :(pacs.attrs.$f[1])
  else
    error("subpart $f not found")
  end
end

ACSetInterface.set_subpart!(pacs::StructPACSet, f::Symbol, val) = _set_subpart!(pacs, Val{f}, val)

@generated function _set_subpart!(pacs::StructPACSet{S, Ts}, ::Type{Val{f}}, val::Array{T,n}) where
  {S, Ts, f, T, n}
  s = MSchemaDesc(S)
  @assert n == length(s.doms[f])
  cod = only(s.codoms[f])
  if f ∈ s.homs
    @assert T == Int64
    quote
      @assert size(val) == size(pacs.homs.$f[1])
      pacs.homs.$f[1] .= val
    end
  else
    @assert T == Ts.parameters[findfirst(s.attrtypes .== cod)]
    quote
      @assert size(val) == size(pacs.attrs.$f[1])
      pacs.attrs.$f[1] .= val
    end
  end
end

@generated function _set_subpart!(pacs::StructPACSet, _, val::Nothing)
  :(nothing)
end

end
