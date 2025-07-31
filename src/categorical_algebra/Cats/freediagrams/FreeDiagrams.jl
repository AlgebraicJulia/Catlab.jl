export ThFreeDiagram, FreeDiagram, cocone_objects, cone_objects, diagram_type, 
       fmap, specialize, ob, hom, obset, homset, obmap, hommap
using StaticArrays: StaticVector, SVector

using GATlab, ACSets
import ACSets: objects

import ....Graphs: src, tgt
import ....Theories: ob, dom, codom, hom
using ....BasicSets: FinSet
import ....BasicSets: left, right
import ..Categories: obtype, homtype
import ..Functors: fmap


"""
This is simpler than a `FinDomFunctor` because the domain is not a FinCat but
rather a Graph. We also don't worry about the category structure of the
codomain (e.g. homs need not specify dom/cod, no composition structure). 
To get a real diagram out of this, one must supply a Category with the
appropriate Ob/Hom types which are supertypes of the Ob/Hom types of the 
FreeDiagram.
"""
@theory ThFreeDiagram begin 
  V::TYPE; E::TYPE; Ob::TYPE; Hom::TYPE; FSet::TYPE{FinSet};
  src(h::E)::V;
  tgt(h::E)::V;
  obset()::FSet
  homset()::FSet
  obmap(v::V)::Ob
  hommap(e::E)::Hom
end

"""    A collection of objects and morphisms 

Some diagrams can be interpreted as (co)limit diagrams. These ought implement a
(co)cone_objects method.
"""
ThFreeDiagram.Meta.@wrapper FreeDiagram

obtype(f::FreeDiagram) = impl_type(f, :Ob)

homtype(f::FreeDiagram) = impl_type(f, :Hom)

ob(f::FreeDiagram) = [obmap(f, x) for x in obset(f)]
hom(f::FreeDiagram) = [hommap(f, x) for x in homset(f)]

diagram_type(f::FreeDiagram) = (impl_type(f, :Ob), impl_type(f, :Hom))

src(f::FreeDiagram) = [src(f, e) for e in homset(f)]
tgt(f::FreeDiagram) = [tgt(f, e) for e in homset(f)]

# Informal interface
#####################
""" Not every FreeDiagram can be thought of as having cone_objects """
function cone_objects end 

""" Not every FreeDiagram can be thought of as having cocone_objects """
function cocone_objects end 

""" Informal requirement of FreeDiagram implementations: 
`fmap` takes an function on objects and a function on homs and replaces the 
obs and homs of FreeDiagram while preserving the edges and vertices.
"""
fmap(f::FreeDiagram, o, h, O::Type, H::Type) = 
  FreeDiagram(fmap(getvalue(f), o, h, O, H))

function specialize end 