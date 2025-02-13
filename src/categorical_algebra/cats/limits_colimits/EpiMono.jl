module EpiMono 
export image, coimage, epi_mono

using GATlab: getvalue
using ...Cats


"""https://en.wikipedia.org/wiki/Image_(category_theory)#Second_definition"""
image(f, m::Category) = 
  equalizer[getvalue(m)](legs(pushout[getvalue(m)](f,f))...)

"""https://en.wikipedia.org/wiki/Coimage"""
coimage(f, m::Category) = 
  coequalizer[getvalue(m)](legs(pullback[getvalue(m)](f, f))...)


"""
The image and coimage are isomorphic. We get this isomorphism using univeral
properties.

      CoIm′ ╌╌> I ↠ CoIm
        ┆ ⌟     |
        v       v
        I   ⟶  R ↩ Im
        |       ┆
        v    ⌜  v
        R ╌╌> Im′
"""
function epi_mono(f, m::Category)
  Im, CoIm = image(f, m), coimage(f, m)
  iso = factorize[getvalue(m)](Im, factorize[getvalue(m)](CoIm, f))
  ComposablePair(compose(m, proj(CoIm), iso), incl(Im))
end


end # module