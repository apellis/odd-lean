# Actual reservoir dotted cap rows and cup columns

This is the first literal row attachment from
[CentralMatrixAttachment](CentralMatrixAttachment.md). It concerns the actual
`ProbeReservoir.epsEntry` and `etaEntry` used in the augmented matrices,
with all exponents `n : ℕ`, including zero, and arbitrary full Hom objects
and formal probe contents. No mixed inverse, unit-dot, finite-height, or
matrix comparison hypothesis is imposed.

The producer and occupied consumer pass strict scoped checks with warnings
as errors and both backward transparency flags disabled. The consumer
audits all 19 producer-owned declarations against the standard axiom set.

The generic matrix sums collapse because dot layers are diagonal:

    epsEntry = (first-strand dot)^n ; capImage
    etaEntry = cupImage ; (second-strand dot)^n.

The source `ReservoirDottedAdjunctionRows` then selects the reservoir side
on both letters. The endpoint chart `twoPathEndpointIso` is equality
transport from the actual path functor to the ordered composite of its
two steps. `twoPathReturnIso` removes the double transport of the given
Hom object around its closed sector path. Both are fixed by the endpoint
certificate; they are not extra isomorphism data supplied by a caller.

In those charts, `epsEntry_reservoir` is the power of
`homContentPostDot` followed by the actual `postCap`; the latter is its
specified content-shifted adjunction counit after the prescribed inner
lowering-object transport. `etaEntry_reservoir` is the actual `postCup`
followed by the lowering step applied to the prescribed shifted dot,
raised to the same exponent. Its unit and its inner raising-object
transport are retained. No parity shift or adjunction normalization is
changed. The statements are whole-map identities, so odd and
inhomogeneous vectors are included.

The paired consumer constructs both complete positive-level asymmetric
two-odd ELV factors, their selected left adjunctions, and both proved
multicolour records. It specializes both actual rows at both odd colours
for every exponent. Its Hom input is the identity at the sector with one
strand of each colour on each factor. The literal input to that Hom
contains an independently surviving product of the two odd coefficient
classes, established by the bounded half-turn coordinate injection.
The auxiliary mixed coefficient is zero data: it is unused by these
rows and is not claimed to satisfy `CrossCoeff.IsInverse`. These are
occupied test factors, not a construction of the intended unit-dot
probe.

The remaining attachment is explicit: combine each retained inner
object transport with the outer endpoint chart, identify the result
with `homContentPostCap` / `homContentPostCup`, and then use their existing
`*_coordinates` identities to reach the native factor cap/unit word.
This has not yet identified every principal/mixed block of either
augmented matrix. In particular the residual-error closure memberships
and the comparison on arbitrary Hom objects required for
`CentralInvertible` remain open. Componentwise coefficient bounds do not
supply a uniform nilpotence exponent over a whole weight product.
