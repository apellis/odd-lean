# The regular-probe component of the pre-Hom counit

This is the normalized counit insertion required by
SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2).
The input `preCapInput` is `emptyProbe.comp H`: the complete probe
weight product is retained until its empty-content evaluation.

`ELVProbeWeightPreCap.vacuumPreSourceIso` compares the regular-probe
component of the chosen whole-weight pre-Hom source with
`ProbeVacuumCap.shiftedPreSourceObject`. In order, its factors are:

1. The component of `homContentPreInverseSource`, including the
   prescribed parity-shift removal and associator.
2. The image under `H` of `vacuumCapSourceIso`.
3. The inverse of `ProbeVacuumCap.preSourceComponent`.

`vacuumPreCounit_native` states

```
preHomCounit.total regularProbe ≫ H.map regularIdentification
  = vacuumPreSourceIso.hom ≫ shiftedPreCap.
```

The counit on the left is that of
`homContentPreAdjunction (probeOldRouquierFamily ...) ... leftAdjoints`.
Its defining diagonal Koszul factor is retained when evaluating the
pre-Hom construction, then absorbed by `vacuumLeftCounit_native`.
There is no cap compatibility or moment hypothesis.

The paired consumer applies the equality with the identity output
functor to both odd colours of the asymmetric fixture. It also proves
the shifted cap is nonzero from its top unit column and the nonzero
regular-probe vacuum vector.

## Remaining mixed-bend comparison

This supplies the counit factor in the padded Dx finite expansion.
The complete equality with `ProbeVacuumCap.evaluatedMixedBend` still
requires the raw pre-dot, reservoir append unit, and reservoir dot
comparisons through their endpoint charts. In particular,
`shiftedPreDot_coordinates` retains a Koszul sign and cannot be replaced
by an unsigned transported module dot. Once these comparisons are
supplied, the odd padded coefficient `-q^(r+1)` at `q = -1` equals
`(-1)^r`, and the two ordered finite series have the same terms.
