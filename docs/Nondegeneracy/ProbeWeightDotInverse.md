# Units for probe dots on weight spaces

`ProbeWeightDotInverse.lean` assembles the checked global-content dot inverse on the prescribed weight-product action. At a block with a predecessor it uses the existing component identification and the global-content inverse; without a predecessor the induced component is a zero object. The original weight group and the scalar parameters are retained.

`probeGlobalActionDotIso` has the existing `globalActionDot` as its forward map and proves both inverse products. Its inverse has the colour parity by `probeGlobalActionDotIso_inv_mem`. The theorem `probeGlobalActionDot_isUnit` packages the prescribed dot as a unit of its endomorphism ring, using `End.of` to retain that ring type.

The producer and closed rational odd-colour consumers on the original integer weight group passed strict direct Lean checks, including the owner axiom audit of 28 declarations. Full build with warnings as errors, global axiom audit and concrete consumers passed before research integration in #807. The result is generic in the scalar data, so it also accepts a parameter-twisted scalar datum. This supplies the family-level probe dot input of InvertibleDotProbe.md Section 5, equation (6). Comparison of the whole coefficient-specialized action and prescribed inverse matrices, and fusion/nondegeneracy, remain separate.
