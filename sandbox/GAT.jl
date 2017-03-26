module GAT

@structure Category(Ob,Hom) begin
  type Ob end
  type Hom(dom, codom)
    dom::Ob
    codom::Ob
  end
  
  function id(A)::Hom(A,A)
    A::Ob
  end
  function compose(f,g)::Hom(A,C)
    A,B,C::Ob
    f::Hom(A,B)
    g::Hom(B,C)
  end
  
  # Extra syntax
  compose(fs::Vararg{Hom}) = foldl(compose, fs)
  
  # Unicode syntax
  ∘(f::Hom, g::Hom) = compose(g, f)
  ∘(fs::Vararg{Hom}) = foldl(∘, fs)
end


# Equivalent shorthand definitions
@structure Category(Ob,Hom) begin
  type Ob end
  type Hom(dom::Ob, codom::Ob) end
  
  function id(A::Ob)::Hom(A,A) end
  function compose(f::Hom(A,B),g::Hom(B,C))::Hom(A,C)
    A,B,C::Ob
  end
end

@structure MonoidalCatgory(Ob,Hom) extends Category(Ob,Hom) begin
  function otimes(A,B)::Ob
    A,B::Ob
  end
  function otimes(f,g)::Hom(otimes(A,C),otimes(B,D))
    A,B,C,D::Ob
    f::Hom(A,B)
    g::Hom(C,D)
  end
  function munit()::Ob end
end

@structure Category2(Ob,Hom,Hom2) extends Category(Ob,Hom) begin
  type Hom2(dom, codom)
    A,B::Ob
    dom::Hom(A,B)
    codom::Hom(A,B)
  end
  function id2(f)::Hom2(f,f)
    A,B::Ob
    f::Hom(A,B)
  end
  function compose2(alpha,beta)::Hom2(f,h)
    A,B::Ob
    f,g,h::Hom(A,B)
    alpha::Hom2(f,g)
    beta::Hom2(g,h)
  end
end

end
