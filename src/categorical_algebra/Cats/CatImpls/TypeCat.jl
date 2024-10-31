""" A TypeCat is just a wrapper around a model of a Category """
@struct_hash_equal struct TypeCat{Ob,Hom} <: CatImpl{Ob,Hom}
  m::Model{Tuple{Ob,Hom}}
  function TypeCat(m::Model{Tuple{Ob,Hom}}) where {Ob,Hom}
    implements(m, ThCategory) ? new{Ob,Hom}(m) : error("Bad model")
  end 
end

getvalue(c::TypeCat) = c.m

@instance ThCategory{Ob,Hom} [model::TypeCat{Ob,Hom}] where {Ob,Hom} begin
  dom(f::Hom) = dom[getvalue(model)](f)
  codom(f::Hom) = codom[getvalue(model)](f)
  id(x::Ob) = id[getvalue(model)](x)
  compose(f::Hom,g::Hom) = compose[getvalue(model)](f,g)
end


Category(m::Model{Tuple{Ob,Hom}}) where {Ob, Hom} = Category(TypeCat(m))
