# Reservoir-to-probe central bend

This is the reverse mixed principal block needed by the central augmented
matrix attachment for the Brundan–Ellis inversion relation. The source
`ReservoirToProbeBend.lean` treats every formal sector and every object of the
full probe-to-reservoir Hom category. The reservoir EF source requires its
reservoir E edge, and the probe FE target requires its probe F edge. These
are precisely the two path-existence conditions, rather than assumptions
about the coefficient or the matrix entry.

Write ER, FR for the prescribed content-shifted reservoir adjunction at
the lower reservoir edge, and EP, FP for the canonical precomposition
adjunction from `T.leftAdjoints` at the upper probe edge. The selected
source chart is `reservoirCapFactorIso` and the target chart is
`probeCupFactorIso`. The comparison is

```
sigma(XR, YP) = sourceChart.hom ; Cx ; targetChart.inv
Cx = unitP(ER(FR Z)) ; FP.map(aPR(FR Z)) ; FP.map(EP.map(counitR Z)).
```

`sigmaEntry_reservoirToProbe` proves this identity, and
`sigmaEntry_reservoirToProbe_negative` conjugates the negative augmented
principal entry to `-Cx`.

The coefficient `aPR` is computed from the given `CrossCoeff.a`, not
postulated. At the probe-down sector its raw PR diagonal is
`-(mixedJ.hom ; a ; mixedJ.inv)`. The probe return changes the formal
right sector. `reservoirToProbeCoefficientIso` transports this object to
`EP(ER U)` along the computed return identity, including both the probe
content in the reservoir parity shift and the probe weight. Conjugating
the raw diagonal by this equality chart defines
`reservoirToProbeCoefficient`. The prescribed mixed interchange may have
odd degree; no evenness claim or extra sign replacement is used.
`reservoirToProbeCoefficientChart` packages its inverse followed by the
computed equality chart, and `reservoirToProbeCoefficient_eq_neg` states
`aPR = -(K.inv ; a ; K.hom)` for that chart.

The proof selects the unique intermediate paths with sides P,P,R,R,
uses the existing `sigmaEntry_eq_sigmaTerm` and
`sigmaTerm_eq_of_paths`, and computes the cup, crossing and cap entries.
A generic transport lemma eliminates the equal probe weights and formal
contents before specializing to the chosen sector. It carries only
computed object equalities and Hom-object transports, with no assumed
operator comparison. Arbitrary collision blocks in the full Hom object
are retained.

The paired consumer constructs both complete positive-level ELV factors
at the asymmetric two-odd datum. It tests both odd colours at a sector
containing one letter of each colour on each factor, using the identity
Hom. Coefficient data are tested both as the identity and as the actual
odd reservoir dot. Independently, the product of the two odd coefficients
survives in a regular-power input to that Hom. These data do not claim
`CrossCoeff.IsInverse` or central invertibility.

The whole augmented matrix chart, its absent-corner cases and residual
coefficient-ideal closure remain separate attachments. In particular,
this result supplies no bound uniform over an entire formal weight
product.

The producer and paired consumer pass the pinned Lean 4.34.1 strict
checks with warnings as errors and both compatibility transparency
settings false. The consumer audits all 53 declarations owned by the
producer against the standard three-axiom allowlist.
