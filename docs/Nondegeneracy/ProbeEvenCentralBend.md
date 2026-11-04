# Finite expansion of the even vacuum bend

The even branch of SwappedHomInversion §3 (A6), (3)–(5), uses the chosen
rational diagonal `(Y-X)⁻¹`. The actual shifted regular-probe dot `X` is a
unit by `ELVProbeEvenVacuumPolynomial`, the reservoir dot `Y` is nilpotent
at its fixed content, and the moving even parity makes the two commute.
Consequently the diagonal is the negative finite series
`-Σ X⁻(r+1) Yʳ`. Every term has coefficient minus one; the alternating
odd series is not used for this parity.

`ELVProbeEvenCentralBend` transports that same series through the existing
post unit and shifted pre-cap. It uses the existing `postBend_sum` identity,
now exposed from `ELVProbeCentralBend` without changing its proof, so the
chronological order remains inverse pre-dot, prescribed cap, prescribed
post unit, and post-dot powers. The construction is on the actual chosen
regular-probe module and permits other odd colours.

The concrete consumer uses an even moving colour in connected mixed data,
a constructed fixed-content nilpotence exponent, and a nonzero tensor input
carrying the other colour's exterior coefficient. Attachment to the padded
central inverse and the even polynomial-cap/normalized bubble identities
remains separate.

Both producers and the mixed-data consumer pass strict checks, with 15
new-module and 51 shared-bend declarations audited. The existing odd bend
and slide consumer also passes, retaining its 51 and 18 declaration audits.
