# Proposed old dotted-unit boundary

This proposed implementation targets the empty boundary of the existing
Brundan–Ellis (1.13) local Rouquier construction. The prescribed old
missing-colour module inverse, its extracted finite rows and their signed
input naturality are already scoped checked separately.

`inductionVacuumCoefficients` assembles these rows into the existing
`RouquierBoundary.Coefficients` record, retaining the original ordinary
unit and signed dot. Coefficients are zero outside the finite window.
`contentVacuumBoundaryCoefficients` supplies the constructed old module
inverse on every empty-content input module, without an additional
inverse or complete-family premise. Its top coefficient is the raw
inverse row; the normalized left counit retains its separate fixed scalar.

These two boundary sources have not passed their paired producer/consumer
gate. The generic producer has passed its strict source check, including
parity membership, finite reconstruction and entry formulas; no paired
consumer has checked the concrete old specialization, which is unverified. Neither an actual empty/one-letter local
Rouquier pair nor its slides and square relations is asserted here.

Next construct the canonical zero lower cell and the empty local record
from this finite boundary, attach the checked grid inverse families and
dotted fields at one-letter content, and prove the prescribed old
nilHecke/whisker squares before applying the existing adjacent-local
left-adjunction theorem. No Frobenius replacement or normalization change
is proposed. The optional whole-family comparison with preselected caps
is unnecessary: the checked regular-probe and closure-object uniqueness
criterion identifies the rows where the normalization is consumed.
