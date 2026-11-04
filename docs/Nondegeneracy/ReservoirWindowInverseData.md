# Chosen reservoir inverse entries in padded coordinates

This attaches named inverse data to the supported pure-factor transfer in
`SupportedFactorWindowInverse.md`. The downstream use is the reservoir
elimination of `CentralInverse/TwoSector` and the contracted coefficient
comparison of SwappedHomInversion §§4–6. Existence of an inverse does not
by itself identify its entries with the chosen reservoir closure maps.

`Sigma/ReservoirWindowInverseData.lean` defines
`ProbeWindow.CapInverseData` and `CupInverseData`. Each record retains
`principal`, a finite `window`, and all five inverse identities in
`isInverse`. Its `negPrincipal` operation negates the forward and inverse
principal maps and keeps the finite window. This is the sign convention
of the negative central augmented matrix.

For the prescribed `P = elvProbeReservoir ...`, the declarations
`SupportedSectors.reservoirCapInverseData` and
`reservoirCupInverseData` produce these records for the literal padded
reservoir sigma and cap or unit entries. Their hypotheses are,
respectively, `0 ≤ D.h i (P.muM t)` and
`D.h i (P.muM t) ≤ 0`; no occupancy premise is required. The input is a
supported Hom object and an additive evaluation into a preadditive
category with a zero object. Both declarations include height zero.

The construction branches on the actual reservoir source content.
At an occupied source it uses `P.muM_postE i ha`, the prescribed native
postcomposition inverse, and the actual source and target corner charts.
At an absent source it uses the native predecessor
`P.muM t - D.α i`, the supported native roundtrip vanishing theorem, and
the isomorphism from that zero native roundtrip to the padded zero corner.
Each record is built directly from this local inverse; no witness is
selected from the earlier existential theorem.

The occupied `_principal` coordinate lemmas give exactly

    targetCorner.hom ; E(nativeTarget.hom ; Z ◁ local.f' ; nativeSource.inv) ; sourceCorner.inv,

where `local` is literally
`(P.W.loc i (P.muM_postE i ha) (P.muM_postF i t)).invPos hh`
or `.invNeg hh`. The occupied `_window` lemmas give, respectively,

    E(rightUnitor.inv ; Z ◁ local.g'(r) ; nativeSource.inv) ; sourceCorner.inv,
    targetCorner.hom ; E(nativeTarget.hom ; Z ◁ local.g'(r) ; rightUnitor.hom).

At an absent source, both `_principal_of_absent` lemmas give zero, and
the cap `_window_of_absent` lemma gives zero. The unit
`_window_of_absent` lemma retains the displayed inverse-row expression
with the synthetic predecessor and its literal `W.loc.invNeg.g'` entry.
The finite unit rows need not vanish at an absent source.

These equations expose exactly the local entries used by
`CentralInverse/FactorClosures`: its principal closure and inverse-window
boundary equations can be applied after cancellation of the displayed
charts and additive evaluation. The named-data package does not prove
the mixed-bend expansion, positive coefficient membership, residual
inversion, or the final central augmented inverse.

The separate consumer is
`scripts/NonVacuity/ReservoirWindowInverseData.lean`. It retains the
explicit nonzero supported tensor Hom over the two-odd-colour rational
datum with Cartan matrix `[[2,-2],[-2,2]]`, cutoff `20`, and OLD probe
multiplicity `10`. On this object it applies the absent unit record,
its principal and inverse-row equations, and the negative-principal
operation. It also applies occupied cap records and their chosen entry
equations at the opposite local height, and both empty-window records
at height zero. Its strict scoped check audits all 85 owned declarations
of the named-data module, together with all 40 and 15 declarations of
the two transfer dependencies, against `propext`, `Classical.choice`,
and `Quot.sound`.
