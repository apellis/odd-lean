# Joint coefficient and affine PBW detection

The cutoff-independent source submodule `jointPBWWindow` spans the full
polynomial/exterior coefficient basis times the affine PBW basis, bounded
in coefficient weight and in the sum of their integer degrees.
`jointPBWWindow_le_coefficientWindow` and
`jointPBWWindow_quotient_mem_degreeBelow` put it inside the two existing
injection domains. `exists_jointPBWWindow_truncated_injective` therefore
proves injectivity of the literal composite through the coefficient quotient
and the actual `truncatedIdeal`. The latter contains both the cyclotomic
ideal and the weighted coefficient ideal, including odd generators.

`jointPBWWindow_detected_at_high_cutoffs` supplies one cofinal bound for a
window fixed before any cutoffs. Its coefficient condition covers all
colours, including those outside the boundary content. The result uses
homogeneous parameters and a positive integral symmetrizer over a
commutative ring; it does not assume flatness of the coefficient quotient,
finite dimension, action faithfulness, or an even coefficient algebra.

Producer and concrete consumers pass pinned direct Lean with warnings as
errors and both compatibility settings. All 12 owned declarations pass
the consumer axiom audit. A nonzero odd exterior coefficient times a
mixed crossing survives both ideals for every sufficiently large common
cutoff; the vacuum instance is also checked. Full build with warnings as errors, global axiom audit and concrete consumers passed before research integration.

This supplies the joint detection input to SwappedVacuumCoordinates §6,
not the action itself. Descent of the categorical inverse and full action
to the weighted coefficient quotient, the normalized vacuum comparison,
remain separate. The exact source-window comparison needed by recovery is verified in #820.
