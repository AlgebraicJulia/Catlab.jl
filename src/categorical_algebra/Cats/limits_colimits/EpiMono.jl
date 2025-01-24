module EpiMono 
export image, coimage, epi_mono

using .....Theories: ⋅
using ...FreeDiagrams
using ..Equalizers, ..Coequalizers, ..Pushouts, ..Pullbacks


"""https://en.wikipedia.org/wiki/Image_(category_theory)#Second_definition"""
image(f) = equalizer(legs(pushout(f,f))...)

"""https://en.wikipedia.org/wiki/Coimage"""
coimage(f) = coequalizer(legs(pullback(f,f))...)

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
function epi_mono(f)
  Im, CoIm = image(f), coimage(f)
  iso = factorize(Im, factorize(CoIm, f))
  return ComposablePair(proj(CoIm) ⋅ iso, incl(Im))
end

end # module
