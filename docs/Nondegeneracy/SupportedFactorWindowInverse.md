# Pure factor inverses on supported sectors

This is the pure-corner inverse attachment needed by
`CentralMatrixAttachment.md` and `SwappedHomInversion.md` §§2, 4–6.
It concerns the prescribed OLD probe and truncated ELV reservoir, with
the actual normalized probe left adjunction and reservoir right
adjunction. It does not assume invertibility of a central matrix or of
its residual.

## Transport and absent corners

`Sigma/FactorWindowInverse.lean` extracts the five cap or cup inverse
equations from `SuperSumInvTo` or `SuperSumInvFrom`. The declarations
`FactorWindowInverse.cap` and `.cup` retain the specified principal and
window entries. `ProbeWindow.IsCapInverse.map` and
`ProbeWindow.IsCupInverse.map` preserve these equations under any additive
evaluation functor. Their `.coordinates` theorems transport the entries
through source and target corner isomorphisms. The `.neg_principal`
theorems negate both principal entries and retain the window entries;
this is the sign required by the negative augmented factor matrix.

For occupied corners, the four
`ProbeReservoir.centralPaddedReservoir_capInverse`,
`centralPaddedReservoir_cupInverse`, `centralPaddedProbe_capInverse`, and
`centralPaddedProbe_cupInverse` theorems apply these operations to
`homContentPostInvPos`, `homContentPostInvNeg`,
`homContentPreInvPos`, and `homContentPreInvNeg`, respectively. Thus their
forward entries are the actual `centralPaddedSigma`, `centralPaddedCap`,
and `centralPaddedUnit` entries, rather than maps defined by inverse
transport.

At an absent reservoir source, take a native weight predecessor and the
native postcomposition roundtrip. At an absent probe target, take a
native probe weight predecessor and the native precomposition
roundtrip. The four companion `_of_source_isZero` and
`_of_target_isZero` theorems transport the same prescribed local inverse
through an isomorphism between that proved zero native object and the
literal padded zero corner. Zero padding of the forward matrix alone
is not used as an inverse argument.

`Sigma/SupportedFactorWindowInverse.lean` discharges those native
vanishing premises. `SupportedSectors.reservoirSource_absent_isZero`
uses the preserved input parity shift and
`ContentHomSupport.postF_supported_absent_isZero` before applying native
post-induction. `SupportedSectors.probeTarget_absent_isZero` applies
`ContentHomSupport.preE_supported_absent_isZero` before the prescribed
shifted pre-restriction. These are whole-functor vanishing statements on
replete exact-content Hom objects; they do not assert vanishing of an
entire original-weight fibre.

## Supported inverse interface

Put `P = elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR`, let
`Z : SupportedSectors.H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t`,
and let `E : P.H t ⥤ C` be additive, with `C` preadditive and possessing
a zero object. The following four declarations supply entrywise inverses
of the actual pure padded corners at every sector:

| Declaration in `SupportedSectors` | Local height condition | Window |
|---|---|---|
| `reservoir_capInverse` | `0 ≤ D.h i (P.muM t)` | native reservoir caps, count `(D.h i (P.muM t)).toNat` |
| `reservoir_cupInverse` | `D.h i (P.muM t) ≤ 0` | native reservoir units, count `(-D.h i (P.muM t)).toNat` |
| `probe_capInverse` | `D.h i (-P.muP t) ≤ 0` | normalized probe caps, count `(-D.h i (-P.muP t)).toNat` |
| `probe_cupInverse` | `0 ≤ D.h i (-P.muP t)` | normalized probe units, count `(D.h i (-P.muP t)).toNat` |

Each conclusion is `∃ j A, IsCapInverse ... j A` or
`∃ j B, IsCupInverse ... j B`. Occupancy is not an additional hypothesis.
Both weak inequalities include height zero and the empty finite window.
The probe normalization, including its gamma and finite triangular
window changes, remains inside the prescribed precomposition inverse.

The paired consumer is
`scripts/NonVacuity/SupportedFactorWindowInverse.lean`. It constructs a
nonzero supported tensor Hom over `ℚ` for two odd colours with Cartan
matrix `[[2,-2],[-2,2]]`, cutoff `20`, and OLD probe multiplicity `10`.
The selected formal content is empty, while another nonempty block at
the same original weight has colour predecessors. The two missing
native corners therefore vanish by exact support, although the input
Hom object and its original-weight fibre are not vacuous. The consumer
also applies the opposite height orientations and all four height-zero
interfaces. Its strict scoped check audits all 40 declarations of
`FactorWindowInverse` and all 15 declarations of
`SupportedFactorWindowInverse` against `propext`, `Classical.choice`,
and `Quot.sound`.

## Chosen reservoir entries for contracted coefficients

The existential interface suffices for the algebraic elimination in
`CentralInverse/TwoSector`. The contracted coefficient comparison needs
more: its reservoir principal `jR` and finite inverse windows must be
identified with the same chosen entries of `P.W.loc` used in the native
reservoir closure calculations.

The separate named-data attachment is
`Sigma/ReservoirWindowInverseData.lean`. Its intended interface is a cap
or cup record with fields `principal`, `window`, and `isInverse`, built
directly from the prescribed local record. The principal coordinate is

    targetCorner.hom ; E(nativeTarget.hom ; Z ◁ local.f' ; nativeSource.inv) ; sourceCorner.inv.

For cap inverse columns it is

    E(rightUnitor.inv ; Z ◁ local.g'(r) ; nativeSource.inv) ; sourceCorner.inv,

and for unit inverse rows it is

    targetCorner.hom ; E(nativeTarget.hom ; Z ◁ local.g'(r) ; rightUnitor.hom).

Here `local` is literally `(P.W.loc ...).invPos hh` or `.invNeg hh`.
The named-data declarations are a separate attachment from the scoped
transfer pair above. Their coordinate equations must be checked before
using them to rewrite contracted residual entries into native reservoir
closures. Positive coefficient membership, finite mixed-bend
comparisons, residual inversion, and the final central augmented inverse
are not conclusions of this pure-factor transfer.
