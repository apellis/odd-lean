# The probe vacuum precomposition adjunction

The source route is the existing finite-local constructor
`SuperRouquierLoc.negativeLeftAdjunction` in
`RouquierAdjacentLeftAdjunction`, specialized to the constructed old
empty-content local record and its adjacent one-letter local record.
There is no separate Frobenius construction and no complete-family input.

The empty record has the zero lower cell in the existing module category
and the actual append induction/restriction as its upper edge. Its lower
crossing is zero. The lower square and the adjacent braid are therefore
zero identities; the braid does not require an additional relation of the
upper crossing. The adjacent local height is
`-contentCrossingHeight([i]) = -cutoff i + 2`, using the Cartan diagonal 2.
Transport along this height equality retains the chosen generator fields.
The only nonzero square input is the actual upper equal-crossing square.

Once the adjacent record is supplied by its native construction, the
existing finite-local left adjunction is retagged from
`p*(-P+1)` to `(P-1)*p`. Its counit is the prescribed fixed diagonal Koszul
factor times the inverse-defined raw capL. The already checked actual
`probeVacuumLoc_cap_total` and closure comparison identify that raw cap on
T0 and F(E(T0)) without a local-record premise.

The existing unshifted precomposition-adjunction constructor retains the
canonical parity comparison. Its second diagonal Koszul factor cancels
the counit's fixed normalization, giving exactly `shiftedPreCap`, with the
raw shifted pre-dot retained. This is the intended attachment of the
chosen evaluated mixed bend to the constructed precomposition counit.

The current source contains only the checked private zero-braid, height
transport and height arithmetic helpers. The public constructed adjunction
and its occupied paired consumer remain proposed until the adjacent native
local record and square are attached. This file is not exported. No
complete swapped factor, mixed inverse or bubble-series claim follows from
these helpers alone.
