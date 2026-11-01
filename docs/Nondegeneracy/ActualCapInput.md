# Actual cap and input dot on arbitrary old Hom endpoints

Status: proposed Lean source and consumers, unchecked pending CI and upstream actual module stack.

ELVOldAppendDot constructs the actual old append dot using the existing full-coefficient appended component and proves its supernaturality. ELVActualCapInput defines contraction from the actual shifted counit followed by total output parity, and input dot from the actual induction dot composed with actual shifted source grading. Actual coefficient(1) shifts the source grading: its tensor formula carries an extra minus. It proves the full-coefficient contraction and input-dot tensor formulas with arbitrary old endpoints, and defines the corresponding maps on the literal Source via coefficientOneSourceEquiv.

Remaining: source checks, agreement with diagonal raw input-defect maps, higher dotted-counit normalization, arbitrary-endpoint boundary leading/division, and action-level natural isomorphisms. No diagonal-to-arbitrary inverse inference is made.

Includes known upstream canonical parity-instance and consumer-namespace repairs locally, preserving #769's first diagnostics run.

## Arbitrary-Hom actual cap pivots

The draft `ELVOffDiagonalActualCapPivots` compares the literal actual
source maps with q of the full-coefficient append formulas on every balanced
generator. Thus actual E and X are used directly, with no repeated quotient
descent and no prescribed row supplied as a hypothesis. The coefficient(1)
shift is retained: X is the actual induction dot after shifted source grading.

Decoding the actual long section gives a source coordinate y. The actual
identities X y(f)=y(rho f) and E y(f)=A(rho f)(0) imply that E X^r on the
degree-d corrected lift vanishes below the anti-diagonal and equals exactly
`offDiagonalBoundaryLeadingEquiv ... 0` on its pivot. Both old endpoints
are arbitrary; the moving colour is odd and all exterior coefficients remain.

A connected mixed B2 consumer reverses source/target words and uses repeated
odd colour at negative height. It checks the actual pivot and the actual
dot/q representative bridge; the production owner has an axiom audit.
These additions and their actual-module/leading-coordinate prerequisites
await CI. They supply the concrete matrix inputs; the full arbitrary-Hom
augmented inverse and normalized unshifted categorical rows remain separate.
