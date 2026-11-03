# The prescribed distinct mate on untruncated old content

This proves the pointwise coend inverse needed for Brundan–Ellis (1.12)
on unweighted, untruncated old-content modules:

    Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k).

Fix lower content ν and distinct colours i,j. The input module N has
content j+ν; the output is evaluated at content i+ν. The positive crossing,
unit and counit are prescribed independently of the inverse.

Use four append functors: j from ν to j+ν, i from ν to i+ν, i from j+ν
to i+j+ν, and j from i+ν to that same upper content. The last functor
`oldContentDistinctUpperAppend` retains literal old append on words and
arrows; only the permutation certificate of its content index changes.

`ELVInductionRectangularMate` uses the chosen induction-composition maps
for the rectangular crossing. Its mate uses the actual upper j-adjunction
unit and lower j-adjunction counit. On a complete balanced tensor the
output coefficient is

    crossing(j,i;s) ≫ twist_(p(i)p(j))(append_j(g)).

No homogeneity hypothesis is imposed on g or the input-module element.
This retains the signs of every exterior coefficient.

The selected source comparison is the chosen content i-induction
comparison followed by old i-induction of the chosen j-restriction
extension comparison. An ordinary coefficient-coend equivalence then
identifies native restriction coordinates with `append_j ⋙ N.toFunctor`.
On source tensors this composite inserts exactly the inclusion unit into
the input coefficient. The selected target map is the chosen upper
content i-induction comparison evaluated at the upper j-append; it inserts
the same unit and retains the entire coefficient arrow.

`oldContentDistinctMateLinear_square` proves the whole linear-map identity

    targetChart ∘ prescribedContentMate = prescribedOldMate ∘ sourceChart.

The old leg is `Distinct.moduleMateLinear`, whose constructed inverse is
`Distinct.moduleMateUnderlyingEquiv`; see
[DistinctModuleInverse](DistinctModuleInverse.md). Both chart maps are
bijective by their chosen module isomorphisms and the ordinary coefficient
coordinate equivalence. `ELVInductionIsoComponents` fixes their coend
endpoints before specializing the categories. Consequently
`oldContentDistinctMateLinear_bijective` proves bijectivity of the actual
content operator without a new invertibility input.
`oldContentDistinctMateEquiv` packages its inverse, and
`oldContentDistinctMateEquiv_toLinearMap` retains exactly the prescribed
positive forward map. The only colour hypothesis is `i ≠ j`.

All four producers and the paired consumer pass strict scoped checks.
The consumer audits all 139 owned declarations and uses shifted old
representables for both mixed moving parities and distinct odd colours,
odd exterior coefficient arrows, an inhomogeneous identity-plus-exterior
arrow, the inverse roundtrip, empty lower content and zero cutoff.
Full CI remains the integration gate.

Further obligations are bundling this pointwise inverse as a homogeneous
old-content module map, input-module naturality of the inverse, canonical
coefficient-truncated `ContentModules`, and original-weight transport.
