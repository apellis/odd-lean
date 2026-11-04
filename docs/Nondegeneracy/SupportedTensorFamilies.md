# The chosen whole-sector tensor-vacuum row

`tensorTargetFamily` is the specified `tensorVacuum` at formal sector
`(0,0)` and `supportedZero` at every other formal sector. The padding is
an exact-content constant zero functor, realized in the whole original
weight products. Its zero-object proof covers every input and every
output block, including other contents of the same original weight.

For each fixed source word `s`, `tensorSourceObject s` is the literal
supported reservoir-path value on `tensorVacuum` for the labelled word
`wd D (ΛP - ΛR) (upWord s)`. `tensorSourceFamily s` retains this object
at `(0,content(s))` and zero elsewhere. It retains the specified word
`s`; it does not select an arbitrary representative of its content.
The prescribed even `tensorSourceObjectIso` identifies it with the
selected tensor word Hom before any regular-input observation.

The terminal matrix sector has original weight exactly `ΛP - ΛR`.
`tensorWordMatrixModule s t` is the existing full supported matrix module
for these whole-sector families at the labelled target word `t`.
`tensorMatrixVacuum s` is the matrix whose occupied source-to-vacuum
entry is the identity of the actual source-word functor and whose other
entries vanish. Thus the construction supplies the fixed-source invariant
row needed by the fixed-source `VacuumCornerEvaluation`; it does not
replace the action by quotient coordinates.

The paired consumer uses the two-odd affine collision datum and carries
the nonzero independent exterior-product source into this matrix. It
also distinguishes the nonzero source formal sector from `(0,0)`, even
though its root content is zero. The producer has passed scoped checks;
the paired consumer requires verification before the result is promoted.
A source-row coordinate equivalence, layer compatibility, source-placed
coefficient action and bubble comparison remain separate attachments.
