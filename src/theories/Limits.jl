export CategoryWithProducts, CompleteCategory

""" Theory of a *category with (finite) products*
"""
@signature Category(Ob,Hom) => CategoryWithProducts(Ob,Hom,Lim) begin
  """ Limit cone, consisting of an apex object plus a finite number of legs.
  """
  Lim()::TYPE
  apex(lim::Lim())::Ob
  
  Lim(foot1::Ob, foot2::Ob)::TYPE
  apex(lim::Lim(A,B))::Ob ⊣ (A::Ob, B::Ob)
  leg1(lim::Lim(A,B))::(apex(lim) → A) ⊣ (A::Ob, B::Ob)
  leg2(lim::Lim(A,B))::(apex(lim) → B) ⊣ (A::Ob, B::Ob)
  
  terminal()::Lim()
  product(A::Ob, B::Ob)::Limit(A,B)
  #factorize(lim::Lim(), C::Ob)::Hom(C, )
end

""" Theory of a *(finitely) complete category*
"""
@signature CategoryWithProducts(Ob,Hom,Lim) => CompleteCategory(Ob,Hom,Lim) begin
  Lim(ob::Ob)::TYPE
  apex(lim::Lim(A))::Ob ⊣ (A::Ob)
  
  #equalizer(f::(A → B), g::(A → B))::Lim(A) ⊣ (A::Ob, B::Ob)
  #factorize(lim::Lim(A), h::Hom(C,A))::Hom(C,)
end
