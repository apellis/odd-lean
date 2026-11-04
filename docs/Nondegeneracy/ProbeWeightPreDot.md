# The raw pre-Hom dot on the whole-weight regular probe

This is the source-dot comparison for SwappedActionAssembly F2 and
SwappedVacuumNonpositiveBubbles §1 (2).

`ELVProbeWeightPreDot.vacuumPreDot_source` evaluates the actual
`homReservoirDot` on the chosen shifted pre-Hom object and carries it
through exactly `vacuumPreSourceIso`, the source chart already used by
the normalized pre-Hom counit. The result is the literal
`ProbeVacuumCap.shiftedPreDot`.

The proof retains the super-interchange sign at both ends. The first
comes from the whole-weight source parity shift. The second comes from
the native shifted pre-dot coordinates. The cutoff/weight equality
identifies their parity exponents. Between them the unsigned underlying
loop dot uses the checked `vacuumLoopDot_source` square. Three typed
ordinary squares compose these statements without a dot compatibility
premise.

The paired consumer uses both odd colours of the asymmetric fixture,
the identity output functor, the native odd polynomial, and the nonzero
regular vacuum vector.
