# Global and local whole-Hom layer charts

SwappedVacuumCoordinates §§5–7 attaches the literal native layer on the
global original tensor row to the prescribed local dot and crossing
operators. `SwappedAssembly/SupportedTensorEntryLayerCharts.lean`
provides these whole-Hom conjugacies for the complete `swappedGens`.

Let `E` be the canonical input-weight equivalence, `m` the actual native
layer entry, `gS,gT` its global row charts and `eS,eT` the specified
local layer charts. Write

```
b   = E.functor.preimage (gS.inv ≫ m ≫ gT.hom),
raw = E.functor.preimage (eS.inv ≫ m ≫ eT.hom),
τS  = E.functor.preimageIso (gS.symm ≪≫ eS),
τT  = E.functor.preimageIso (gT.symm ≪≫ eT).
```

The derived square is `b ≫ τT.hom = τS.hom ≫ raw`. It is a statement
on the full original Hom, before evaluation or quotient coordinates.
The global operator is `tensorOriginalWordLayer`; the local operators
are the frozen `tensorLayerDotRaw`, `tensorLayerSameCrossRaw` and
`tensorLayerCrossRaw`. The three `_arrow` declarations identify these
local operators with the exact entries of the full chosen action.
Only the upward dot or crossing field is used in each identification.

`tensorOriginalWordLayer_dot`, `tensorOriginalWordLayer_sameCross` and
`tensorOriginalWordLayer_cross` give the conjugacy for whole-Hom chart
data. Their concrete consumers supply `gS,gT` from the actual
`tensorRowTargetIso`. No generator-comparison equation is assumed.
Both outer reservoir paths and the distinct crossing's endpoint
transport are retained. The existing `tensorLayerDotAt_eq`,
`tensorLayerSameCrossAt_eq` and `tensorLayerCrossAt_eq` give the
prescribed endpoint-weight transports of the same local operators.

The local categorical calculation is parameterized by its sector
content directly. The global source-word content is substituted only
after that square is proved. This preserves the same paths and maps
while preventing repeated expansion of the source-word labels during
type checking.

Compatibility of these whole-Hom chart changes with their values at
the regular probe is a separate attachment. The existing heterogeneous
equalities of global and local value charts do not by themselves
assert this compatibility. The subsequent quotient observation must
retain the resulting value square.

The paired consumer uses the two-odd collision datum and homogeneous
zero-interior parameters. The distinct-word fixture has source word
`[true,false]`; a second fixture has the repeated word `[true,true]`.
Bounded coordinate injectivity proves nonzero full matrix vacua and
nonzero modules of the complete action in both fixtures. All dot,
equal-colour and distinct-colour layer paths, endpoints and upward
certificates are constructed. The consumer also checks the frozen
`At` identifications on those same paths and audits owned declarations
and the constructed nonzero-vector proofs against the standard axiom
allowlist.
