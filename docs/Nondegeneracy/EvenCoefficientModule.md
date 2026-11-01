# Even coefficient module and adjunction source

This supplies the even-colour source comparison needed by [DeformedMatrixComparison §4](DeformedMatrixComparison.md).

For an even moving colour, coefficient(0) is canonically the ordinary restricted representable as a supermodule. The pointwise identity respects both projections and every old action. The comparison is constructed before induction, so no dependent transport is applied to the balanced coend. `coefficientRestrictionModuleIso` and `evenMovingCoefficientIso` supply these comparisons. Their induced components give `evenSourceEquiv`, the canonical even map from the ordinary Ind–Res source to the literal balanced crossing source.

`unshiftedCounitComponent` is the component of the existing ordinary adjunction counit. `evenSourceInputContraction` transports its negative through this canonical source equivalence. The theorems `evenSourceInputContraction_counit` and `evenSourceInputContraction_tensor` prove respectively

\[
E_0(J_0z)=-\varepsilon(z),\qquad E_0(g\otimes b)=-\operatorname{oldComp}(b,g).
\]

The minus is constant; there is no odd higher-row scalar or output twist in this even-colour statement. Identification with the raw even input operators and the actual dot remains a separate step. No mate identity or categorical inverse is asserted here.

The producer is `ELVEvenCoefficientModule.lean`. Its concrete consumer uses an even moving colour, an odd coefficient of the other colour and a mixed crossing over two colours. The exact weighted quotient detector proves the test vectors nonzero for every sufficiently large cutoff. The producer and consumer pass strict scoped checks, and all 50 owned declarations pass the scoped axiom inventory. Full CI is required before integration; see [STATUS](STATUS.md) for integrated results.
