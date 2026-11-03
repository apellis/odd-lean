# Local inverse data on an actual zero lower loop

Brundan–Ellis (1.13)–(1.14) require the local record even when the lower
predecessor is absent. `SKM.RouquierZeroLocal.ofCoefficients` works in an
arbitrary linear 2-supercategory. Its inputs are the two given adjunctions,
the upper dot and its constructed boundary coefficients, and the equations
that the actual lower loop and double upward cell have zero identity.
No particular zero functor or zero category is required by the theorem.

The lower dot and crossing are zero. Both slide equations use the actual
double-cell identity equation. The negative inverse retains the prescribed
upper unit columns and every given coefficient row, with a zero principal
inverse. The `ofCoefficients_invNeg_g'` theorem retains each row after height
normalization. At height zero the coefficient total forces the upper-loop
identity to vanish, so both positive and negative inverse orientations are
constructed from the same inputs.

The exact producer and paired consumer pass strict checks with warnings as
errors and both compatibility settings. All 35 owned declarations pass the
axiom allowlist. The consumer uses the checked missing-colour OLD matrix
coefficients in both moving parities, including nonempty mixed content.
It proves that the actual local inverse top row returns a nonzero full PBW
ground vector. At zero cutoff both orientations and their matrix identities
are tested, alongside the nonzero height-zero regular probe vector.

The boundary coefficient record is an explicit intermediate input supplied
by the constructed matrix. This theorem does not assume a local inverse or
global action relation. Transport to selected global coordinates remains a
separate application.
