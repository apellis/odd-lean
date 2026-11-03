# The normalized cap on the evaluated tensor vacuum

`ELVTensorVacuumCap` attaches the normalized boundary inverse cap to the
same module on which the evaluated mixed bend acts. This is the operator
alignment required by `InverseCapMoments` and `NegativeCapMoments` in
`SwappedVacuumCoordinates.md`, §6.

Write `e : H(N0) ≅ W0` for the actual even `probeVacuumIso`, `G` for the
prescribed canonical-content F/E functor, and `lambda_W` for the native
regular power-vacuum cap. The definition is precisely
`G(e.hom) ≫ lambda_W ≫ e.inv`. The given unit/dot columns intertwine under
this chart: their even-input naturality is proved before specifying the
cyclotomic category, allowing rectangular append functors.

`tensorPowerVacuumCap_eq_inverseRow` uses the existing joint-epimorphism
inverse identities to identify this transported cap with the last row of
every inverse of the given native boundary columns on `H(N0)`. The proved
absent-colour inverse supplies those rows without an inverse premise. The
cap retains its exact degree `(cutoff i - 1)*p`.

`tensorPowerVacuumCap_compare` is a whole module square through `e`, so the
cap has the same literal-T scalar decoding as the original reservoir cap.
`tensorPowerVacuumCap_window` proves the exact `u ; y^a ; ell` Kronecker
window on the tensor carrier, using the given ordinary unit and restricted
dot. No independent extraction functional is chosen.

The exact producer and paired consumer pass strict scoped Lean checks.
All 50 owned declarations, including private and generated ones, pass the
standard axiom audit. The consumer uses the occupied asymmetric all-odd
literal power vacuum with reservoir cutoffs 4 and 5 and powers 4. Both caps
are nonzero, equal the constructed inverse rows, retain their degrees and
whole comparison squares, and satisfy the operator window for all vectors.
Full repository CI remains the integration gate.

The next step uses this cap together with the already proved evaluated
mixed-bend slide and signed probe polynomial. The complete swapped matrix
and bubble-series identification are not asserted by this module.
