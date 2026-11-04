# Distinct-colour sideways permutation

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5,
(1.11), requires the sideways crossing for distinct colours to be an
isomorphism. For the supported Hom construction, the sector contents
record the side of each colour. Hence the two summand paths at fixed
endpoints are unique, and the two words have paths simultaneously.
`ProbeReservoir.sigmaPermutation_of_isIso` reduces the permutation
statement to invertibility of the four possible entries.

`CyclotomicAction.elvProbeSigmaPermutation_of_pureEntries` is the
intermediate assembly for the prescribed ELV probe and reservoir. Its
sole remaining premise states invertibility of the two pure entries,
for every colour pair, weight, endpoint sector and Hom object. The
probe/reservoir entry follows from the constructed source polynomial
units in `elvProbe_distinct_sigmaEntry_isIso`; these retain contentwise
reservoir nilpotence and do not assume a common nilpotence exponent.
The reservoir/probe entry is the invertible mate of the interchange,
`ProbeReservoir.isIso_sigmaEntry_reservoir_probe`.

The pure probe entry must be identified with the left mate of the
probe factor crossing. `SKM.LeftMateInvertible` is the exact factor
input to `SKM.homContentDistinctPreMate_isIso`. This input is an
intermediate hypothesis: it is not implied by arbitrary chosen left
adjunctions together with `RouquierMulticolour.invNe`, which controls
the right mate. Its removal requires the prescribed factor left
rotation and inverse relations.

The pure reservoir entry must be identified with the right mate of
the reservoir crossing, including the prescribed content parity
comparisons. The factor right mate is invertible by `invNe`. The
comparison between the even beta/xi pair chart and successive
homogeneous parity removals is equation (4) of
[MixedColourBlockCompletion](MixedColourBlockCompletion.md). For
content shifts `p=b p_i`, `q=b p_j` and crossing degree `r=p_i p_j`,
its naturality sign is trivial because `(p+q)r=0` in `ZMod 2`.

The consumer `scripts/NonVacuity/ELVProbeSigmaPermutation.lean`
instantiates the intermediate assembly over the mixed-parity Boolean
weighted fixture. It checks both mixed entries on the prescribed Hom
categories and a nonzero probe vector. It retains the pure-entry
premise explicitly and does not claim an unconditional sideways
permutation or a resulting completed action.
