# The regular coefficient-power vacuum on the old category

This constructs the literal old vacuum in [SwappedNondegeneracy, §2](SwappedNondegeneracy.md)
from the actual regular A/T module of [CoefficientPowerGrading](CoefficientPowerGrading.md).
Both producers and the paired occupied consumer pass scoped Lean checks with
warnings as errors and both pinned compatibility settings. All 35 owned declarations
of `ELVEmptyCoefficientEmbedding` and all 64 of `ELVCoefficientPowerVacuum`
pass the standard axiom allowlist audit. Full CI remains the integration gate.

## The empty coefficient embedding

The affine-empty PBW coordinate decodes the coefficient of its identity.
There is no first-position old cyclotomic relation at the empty word, and
`vacuum_hom_span` spans its entire Hom by the full coefficient identities.
Thus `emptyCoefficientEquiv` identifies A with the complete old empty-word
Hom. Its encoder and decoder are inverse on every coefficient and every
old empty-word arrow. No monic-basis or oriented coefficient-independence
hypothesis is added.

`emptyCoefficientEmbedding` consequently embeds the original one-object
coefficient supercategory fully faithfully at the empty old word. It is
additive, linear and parity preserving, and retains the exact composition
order e(a) composed with e(b)=e(b*a).

## The actual old power vacuum

The existing balanced-induction implementation requires its source and
target object universes to match. An object-only ULift raises the unique
coefficient object while keeping every coefficient Hom, vector and map
unchanged. `powerCoefficientEmbedding` is this lifted fully faithful
embedding, and `liftedPowerRegular` is the same regular A/T module on it.

`coefficientPowerVacuum` is their actual balanced induction to the old
category. The existing fully faithful unit isomorphism supplies
`coefficientPowerVacuumUnitIso`. Its original even balanced unit and
prescribed inverse give `coefficientPowerVacuumEmptyEquiv` from literal
A/T to the empty old-vacuum component. This identification preserves every
coefficient parity. It does not impose an additional weighted quotient.

At a nonempty old word, every incoming Hom from the empty coefficient
object is zero by content support. Balanced-tensor generation therefore
proves `coefficientPowerVacuum_support`: all nonempty components vanish.
For each even power generator of T, its old coefficient endomorphism
slides through a tensor and balances onto the regular coefficient module,
where it acts as zero. The proved generator characterization of the
two-sided annihilator gives `coefficientPowerVacuum_property` for the
entire literal ideal T on every component. `coefficientPowerVacuumObject`
is therefore an actual object of the preserved T-annihilated category.

The connected two-odd-colour consumer at cutoff four checks the chosen
unit inverse, complete coefficient decoding, append restriction zero and
whole-ideal annihilation. Both independent odd coefficient classes are
proved nonzero in the actual empty old-vacuum component and retain odd
parity through its chosen even unit comparison.

## Boundary

This is the regular power vacuum of the old full-coefficient module
category, not yet the final swapped action's normalized vacuum. Attaching
the inverse coefficient rows to this module is proved separately in
[CoefficientPowerRows](CoefficientPowerRows.md). The mixed inverse caps,
integer grading and explicit positive-dot bounds remain separate.
No positive-dot nilpotence is inferred from finite dimension alone. The
actual vacuum evaluation kernel and all-height bubble theorem remain open.
