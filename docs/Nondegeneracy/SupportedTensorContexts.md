# The tensor vacuum in both reservoir contexts

`SupportedSectors.tensorContextIso` specializes the existing prescribed
reservoir-context chart to `tensorVacuum`, the literal supported selected
tensor Hom. The middle factor morphism is unchanged. Both labelled outer
paths remain present, including an arbitrary nonzero terminal content of
the left path.

`tensorContext_square` identifies every chosen middle factor map with the
corresponding map on this selected tensor Hom and both reservoir words.
The existing even right-context chart supplies the interchange, so odd
dots and odd crossings introduce no additional sign. The target functor
is literally `ReservoirLayerCells.dotRawHom` or `crossRawHom` when the
middle factor is the prescribed single E or pair of E morphisms. Only
the proved normalization of the vacuum input weight is transported.

The paired consumer uses the affine two-odd datum with Cartan matrix
`[[2,-2],[-2,2]]`, a two-letter right context and a nonempty left context.
It instantiates the chart and square for every Boolean dot colour and
crossing pair, including equal colours. It also applies the existing
all-vector `ReservoirLayerCells` class squares with concrete nonzero
inputs and quotient classes carrying both independent odd coefficients.
Every representative is obtained from quotient surjectivity.

The literal swapped layer matrices still require attachment through
their existing middle-generator charts. These statements compare chosen
factor maps in the specified path contexts; they do not construct the
full presentation action, coefficient/bubble comparison, or final vacuum
observation. No central-inverse or presentation-relation hypothesis is
used for these comparisons.
