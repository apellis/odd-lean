# Proposed original-weight pair crossing comparison

This is an unverified variant outside the checked library. The source
`ELVWeightPairCrossing.lean` is not exported and its whole specialized
comparison has not passed kernel checking.

The proposed identity compares the independently assembled weight crossing
with the canonical content-pair crossing under the two chosen pair object
equalities. The generic comparison argument factors both chosen isomorphisms
as an object equality followed by the content induction comparison. Its
component square is then the existing content-pair crossing square.

The native module-arrow equality still requires large dependent functor
conversions. The next encoding compares the pointwise linear totals directly,
which is the form needed to combine with the existing content quadratic and
the proved weight-dot squares. It must retain the given weight crossing,
both canonical pair coordinates, and the actual absent-predecessor cases.
No crossing compatibility or invertibility premise is to be introduced.
