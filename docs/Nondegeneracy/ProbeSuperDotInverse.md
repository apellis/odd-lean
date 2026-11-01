# Signed inverse of the probe induction dot

`ProbeSuperDotInverse.lean` uses the existing all-height `heightInductionCorner`, `heightInductionDotLinear` and `heightSuperInductionDot`. Thus the construction includes induction from the vacuum and every positive height. The inverse applies right multiplication by the append-corner inverse followed by the parity sign.

The SVec isomorphism and `Supercategory.inv_mem` supply inverse parity. Cancellation proves signed left linearity and ordinary right linearity. On a homogeneous element of parity p, the inverse is sign_k(d+p*d)·(x·X), including the extra sign for an odd induction colour.

`probeHeightInductionSuperDotIso` and `probeHeightSuperDotIso` give the superbimodule and supernatural isomorphisms, with both inverse products. The source retains exactly the polynomial parity input required by the existing action. `probePolynomial_parity` supplies that input for the prescribed probes.

The producer and closed rational odd-colour consumers at vacuum and positive heights have passed strict direct Lean checks, including the full owned-declaration axiom audit. Full build with warnings as errors, global axiom audit and concrete consumers passed before research integration in #807. This supplies the all-height dot input of InvertibleDotProbe.md Section 5, equation (6). Content-block restriction is also verified in #807. The coefficient-specialized comparison of the full action and prescribed inverse matrices, and fusion/nondegeneracy remain separate.
