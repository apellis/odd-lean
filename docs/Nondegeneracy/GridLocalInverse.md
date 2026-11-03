# Inverse entries of the prescribed induction-grid matrices

`gridLocalInverseFrom` and `gridLocalInverseTo` extract `SKM.SuperSumInvFrom` and `SKM.SuperSumInvTo` from an isomorphism whose forward map is precisely the given finite grid unit or cap matrix. The principal field remains `orderedGridMateComponent`, the auxiliary fields remain `unitDotColumn` or `capDotRow`, and their parity profile is exactly `n • p`.

The construction uses the literal `gridUnitMatrixFamily` and `gridCapMatrixFamily`. Their parity-restoring isomorphisms are the chosen `SKM.homParityShiftDatum` coordinates. The specified even entries agree definitionally with the restored columns or rows, so no inverse compatibility, column rescaling or independently chosen forward field is introduced.

These are intermediate constructors for BE (1.13)–(1.14); the matrix isomorphism is an explicit input. The paired concrete consumer supplies constructed inverses of the given old-content matrices, proving the required positive and negative height hypotheses. It checks both moving parities and all inverse/parity identities, including off-diagonal entries. Application to canonical truncated-content and selected weight matrices awaits their constructed matrix inverses and the corresponding field comparisons.

Producer and paired concrete consumer pass scoped strict checking and the owned-declaration axiom audit. Full integration CI remains required.
