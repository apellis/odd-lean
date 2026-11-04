# Distinct-colour sideways permutation

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5,
(1.11), requires the sideways crossing for distinct colours to be an
isomorphism. For the supported Hom construction, the sector contents
record the side of each colour. Hence the two summand paths at fixed
endpoints are unique, and the two words have paths simultaneously.
`ProbeReservoir.sigmaPermutation_of_isIso` reduces the permutation
statement to invertibility of the four possible entries.

`CyclotomicAction.elvProbeSigmaPermutation`
assembles the four entries for the prescribed ELV probe and reservoir.
The canonical probe factor's left mates are supplied by
`RouquierFamily.canonicalLeftMateInvertible`, proved from the
multicolour relations. The probe/reservoir entry follows from the
constructed source polynomial units in
`elvProbe_distinct_sigmaEntry_isIso`; these retain contentwise
reservoir nilpotence and do not assume a common nilpotence exponent.
The reservoir/probe entry is the invertible mate of the interchange,
`ProbeReservoir.isIso_sigmaEntry_reservoir_probe`.

`ProbeReservoir.isIso_sigmaEntry_pure_probe` identifies the pure
probe entry with the precomposition mate of the probe factor crossing,
including the transports between the two orders of adding colours.
Its exact factor premise is `SKM.LeftMateInvertible` for the probe
family and its normalized left adjunctions. The invertibility proof
then uses `SKM.homContentDistinctPreMate_isIso`. This generic factor
premise is discharged for the prescribed canonical adjunctions: the
cap range and the shifted strict cup range cover every weight. The
cap and cup identities follow from the local inverse, mixed braid,
quadratic and dot-slide relations. Arbitrary independently chosen left
adjunctions are not substituted for these canonical adjunctions.

`ProbeReservoir.isIso_sigmaEntry_pure_reservoir` identifies the pure
reservoir entry with the right mate of the reservoir crossing,
including the prescribed content parity comparisons. The factor right
mate is invertible by `invNe`. The theorem `SKM.postPairCrossing_eq`
compares the even beta/xi pair chart with successive homogeneous
parity removals, as in equation (4) of
[MixedColourBlockCompletion](MixedColourBlockCompletion.md). For
content shifts `p=b p_i`, `q=b p_j` and crossing degree `r=p_i p_j`,
its naturality sign is trivial because `(p+q)r=0` in `ZMod 2`.

The consumer `scripts/NonVacuity/ELVProbeSigmaPermutation.lean`
instantiates the permutation over the mixed-parity Boolean
weighted fixture. It checks the mixed entries and the pure reservoir
entry on the prescribed Hom categories and a nonzero probe vector.
Both colour orders have every hypothesis constructed. The separate
consumer `scripts/NonVacuity/DistinctPureEntries.lean` constructs
occupied pure-probe paths explicitly and supplies the canonical
left-mate proof from the chosen factor's multicolour relations.
Owner-module audits check these declarations against the standard
axiom allowlist.
