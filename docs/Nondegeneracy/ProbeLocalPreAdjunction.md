# Finite-local precomposition adjunction of the probe

Source: SwappedHomInversion §1, HomSectorTransport §2 (4), and the existing
negative-height adjacent-local left-adjunction construction.

The producers and paired consumer pass strict scoped Lean checks. The
owned-declaration audits cover all 13 declarations of the generic module
and all 24 of the probe module, including private and generated ones,
using only the standard three axioms. Full-package CI remains the
integration gate.

`SKM.unshiftedPreAdjunction` extracts the already used shift-square transport
from a single shifted left adjunction, without a whole Rouquier family.
Its unit is the given left cup with the canonical output comparison; its
counit keeps the extra diagonal Koszul factor and the given normalized
left cap. Both are even on the full Hom supercategories, giving
`unshiftedPreSuperAdjunction`.

`ProbeVacuumCap.localLeftAdjunction` instantiates the checked
`SuperRouquierLoc.negativeLeftAdjunction` on the given native probe
induction/restriction edge. Reindexing its parity to the last-row degree
does not alter its maps. `localPreAdjunction` and
`localPreSuperAdjunction` construct its precomposition adjunctions;
`localPreAdjunction_counit_total` identifies the constructed counit's
regular-probe component with the prescribed `shiftedPreCap`. The native
normalization and the additional precomposition Koszul factor cancel.
The left unit is unchanged.

The two adjacent local Rouquier records, their squares and braid remain
explicit intermediate inputs. Their construction on these native probe
endpoints is separate; neither a complete factor family nor the mixed
central-entry bend is established here. The consumer tests the nonzero
prescribed component on the native parity-shift Hom object at both
asymmetric odd probe levels, and applies the new comparison to supplied
local records without asserting those records have been constructed.
