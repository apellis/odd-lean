# Distinct-colour sideways permutation

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5,
(1.11), requires the sideways crossing for distinct colours to be an
isomorphism. For the supported Hom construction, the sector contents
record the side of each colour. Hence the two summand paths at fixed
endpoints are unique, and the two words have paths simultaneously.
`ProbeReservoir.sigmaPermutation_of_isIso` reduces the permutation
statement to invertibility of the four possible entries.

`CyclotomicAction.elvProbeSigmaPermutation_of_leftMateInvertible`
assembles the four entries for the prescribed ELV probe and reservoir.
Its sole remaining premise is invertibility of the canonical probe
factor's left mates. The probe/reservoir entry follows from the
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
then uses `SKM.homContentDistinctPreMate_isIso`. This is an intermediate
hypothesis: it is not implied by arbitrary chosen left adjunctions
together with `RouquierMulticolour.invNe`, which controls the right
mate. Its removal requires the prescribed factor left rotation and
inverse relations.

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
instantiates the intermediate assembly over the mixed-parity Boolean
weighted fixture. It checks the mixed entries and the pure reservoir
entry on the prescribed Hom categories and a nonzero probe vector. Its permutation
example retains the canonical left-mate premise explicitly. This does
not provide a closed native permutation consumer or a completed action;
the canonical factor left-mate proof remains to be supplied.
