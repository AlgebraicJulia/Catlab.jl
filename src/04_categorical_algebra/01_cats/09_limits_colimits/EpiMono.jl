module EpiMono 
export image, coimage, epi_mono

using ...Categories: Category
using ...FreeDiagrams: ComposablePair

using ..Equalizers: equalizer
using ..Coequalizers: coequalizer
using ..Pushouts: pushout
using ..Pullbacks: pullback


"""https://en.wikipedia.org/wiki/Image_(category_theory)#Second_definition"""
image(f, m::Category) = equalizer(legs(pushout(f,f, m))...)

"""https://en.wikipedia.org/wiki/Coimage"""
coimage(f, m::Category) = coequalizer(legs(pullback(f, f, m))...)


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
  iso = factorize(Im, factorize(CoIm, f))
  ComposablePair(proj(CoIm) ⋅ iso, incl(Im))
end


end # module