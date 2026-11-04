# The whole-weight probe cap and its OLD coefficient row

This is the cap-coordinate step needed by SwappedActionAssembly F2 and
SwappedVacuumNonpositiveBubbles §1 (2). It compares the whole-weight
probe's inverse-defined raw left cap with its prescribed local cap.

`ELVProbeWeightLeftCap.probeOldWeightLoc_cap_missing` states, at a
negative-height block with no lower predecessor,

```
wholeWeightCap.total M δ =
  eqToHom followingObject ≫ storedMissingCap.total (M δ).
```

The statement applies to every input weight module, retaining its other
content blocks. Its proof uses the actual global dotted-unit columns,
`probeOldWeightUnitPower_total_comparison`, and both inverse records'
finite cap windows. The lower mixed source is zero, so the global
augmented inverse's `hom_ext` identifies the entire outgoing cap map.
There is no cap compatibility or moment premise. In particular the
choices used to assemble `probeOldWeightLoc` do not leave its cap
normalization undetermined.

`ELVProbeMissingCapCoordinates` identifies the stored cap further:

- `probeMissingStoredLoc_cap_eq` gives the top boundary coefficient.
- `probeMissingStoredLoc_cap_chart` transports it by the explicit inverse
  of `probeAppendUpperLoopSuperIso` to the un-reindexed evaluated cap.
- `probeMissingStoredLoc_cap_total_native` forgets the scalar-evaluation
  certificate and retains the full OLD inverse cap at every module.
- `probeMissingBoundary_regular_cap` identifies that OLD boundary cap
  on the original regular probe with `ProbeVacuumCap.cap`. The finite
  unit window used by cap uniqueness is derived from the constructed
  boundary inverse.

The concrete consumers use both odd colours of the asymmetric parameter
fixture. The whole-weight consumer proves the missing-predecessor and
negative-height conditions, applies the chart to arbitrary whole-weight
inputs and to the selected regular probe, and retains its proved nonzero
vacuum vector. The stored-cap consumer checks the coefficient, chart,
native and regular-cap identities with the actual constructed records.

`ELVProbeWeightLeftCounit.probeOldLeftCounit_negative_sign` also
identifies the normalized whole-weight left counit after multiplying by
its diagonal Koszul factor. At negative source height that factor
cancels the prescribed normalization and recovers exactly the raw cap.
`probeOldLeftCounit_missing` evaluates this equality at every input
module and missing block, then applies the same successor chart. Its
consumer proves that the factor is `-1` for both tested odd colours.

`ELVProbeWeightVacuumCap.vacuumCapSourceIso` composes the successor
chart, the stored upper-loop chart, empty-content forgetting, and
`emptyProbe_regular`. It identifies the evaluated whole-weight upper
loop with the literal source of `ProbeVacuumCap.cap`.
`vacuumCapSourceIso_hom_mem` records that this entire source chart is
even. The main equality `vacuumLeftCounit_native` is

```
q • (emptyProbe.map (leftCounit.total regularProbe) ≫ regularIdentification)
  = vacuumCapSourceIso.hom ≫ nativeVacuumCap,
```

where `q` is the prescribed diagonal Koszul sign. This compares full
module maps and uses the actual chosen whole-weight left adjunction.
The consumer checks both odd colours and proves the native cap is
nonzero using its top unit-column pairing and the nonzero regular probe
vector. The public abbreviation `WeightTensorVacuum.emptyContentForget`
exposes the existing forgetting map while preserving its original
private implementation.

## Remaining bend comparison

To identify the padded central bend with
`ProbeVacuumCap.evaluatedMixedBend`, one must still insert the
normalized counit comparison into the pre-Hom construction through
`homContentPreInverseSource` and `preSourceComponent`, and match
the reservoir append unit and both raw dots under the endpoint charts.
The preceding identities retain both the diagonal parity factor and the
left-adjunction normalization; they do not assert that these remaining
bend maps are definitionally equal.

The existing finite series give a direct comparison once those maps
are matched. At odd parity, the padded coefficient `-q^(r+1)` with
`q = -1` is `(-1)^r`, precisely the coefficient of
`evaluatedMixedBend_odd_expansion`. Thus the remaining comparison can
proceed term by term, keeping the inverse raw predot, cap, post unit and
reservoir dot in their prescribed chronological order.

Once that map comparison is supplied, the exact chosen inverse rows in
[VacuumInverseWindow](VacuumInverseWindow.md) can be combined with the
checked tensor polynomial-cap and principal-cap equations. No actual
bubble values are asserted by the present cap-coordinate modules.
