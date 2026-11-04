# The pure reservoir sideways entry

For distinct colours, the pure reservoir entry of Brundan–Ellis
Definition 1.5, (1.11) is the right mate of the given reservoir crossing.
`Sigma/DistinctPureReservoirEntry` compares the literal `sigmaEntry`
on the paths with sides `[false,false]` with this factor mate, retaining
the original cup, crossing, cap and sector transports.

The raising reservoir strand has the content shift
`p = parity(i) contentParity(beta)`; the other colour has
`q = parity(j) contentParity(beta)`. The prescribed beta/xi comparison
for the upward crossing is `homShiftedPostCrossing`, because
`(q+p) parity(i) parity(j) = 0`. The comparison is proved in
`DistinctReservoirShift`, with the general normalization sign retained
before specializing the content shifts.

The same shifted postcomposition adjunctions supply the cup and cap.
After the original endpoint transports, their composite with the
crossing is `homShiftedPostCrossMate`. Its invertibility is exactly
`homShiftedPostCrossMate_isIso`, applied to `P.W` and
`P.reservoirRel`; that theorem uses the reservoir factor's distinct
inversion relation. There is no extra pure-entry or mate hypothesis.
The probe left adjunctions do not enter this pure reservoir argument.

The consumer uses the prescribed ELV probe/reservoir over the rational
numbers with a connected mixed datum. Its concrete two-reservoir paths
have positive raising content, and all path conditions are proved.
The underlying probe vacuum append vectors are nonzero in both colours.
The constructed crossing coefficients come from `ELVProbeDenominatorUnits`;
neither the permutation assembly nor a probe left-mate hypothesis is needed.
It audits all declarations of the entry module against the standard
axiom allowlist.
