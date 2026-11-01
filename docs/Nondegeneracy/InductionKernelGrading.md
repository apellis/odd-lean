# Graded Hom-kernel realization

This supplies the target-kernel grading comparison in
[DeformedMatrixComparison §4](DeformedMatrixComparison.md).
The kernel is the existing ordinary-right Hom(J−,w) from
[InductionKernel](InductionKernel.md).

`inductionKernelGrading` is the actual Hom superspace grading.
`inductionKernel_isGraded` proves its ordinary-right source action has
the prescribed degree using the existing superfunctor structure on J.
`inductionKernel_coefficientProj` identifies every coefficient projector
with the original Hom projector.

`inductionKernelEquiv_even` proves that the identity between the literal
kernel quotient and balanced induction preserves their actual sum gradings,
for every input supermodule. It assumes no grading comparison.

Both source and concrete consumers pass strict checks, including all 8
owned-declaration axiom checks. Consumers retain full old coefficients,
genuinely mixed endpoints, both moving parities and a cofinally nonzero
odd-coefficient mixed-crossing quotient tensor. Full CI remains required;
see [STATUS](STATUS.md).
