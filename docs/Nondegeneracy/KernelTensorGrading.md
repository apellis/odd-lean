# Grading of coefficient-kernel tensors

Current scope and verification are maintained in [STATUS](STATUS.md). Any original
topic-head pending checks below are historical; they do not override the consolidated
status or establish completion of the full conjecture.

The arbitrary-module kernel transport in
[DeformedMatrixComparison §4](DeformedMatrixComparison.md) retains the sum
parity, in addition to the underlying balanced quotient.

`CoefficientGrading K` records odd projectors on the kernel's existing
coefficient modules. `IsGradedKernel K G` requires the ordinary-right action
of a degree-p source arrow to have degree p. This is a property of that
specified action; it is not an identification with a supernatural
representing-source map.

With this property and the actual graded input module, `oddSummand_balance`
proves that the sum projector descends through the literal balance.
`superspace` grades the same quotient and `proj_tensor` gives its complete
two-term projection formula. The source arrow may be inhomogeneous.
`map_even` proves that even natural coefficient-kernel maps remain even
after tensoring with any input module. No flatness, projectivity or
coefficient projection is assumed.

The source and concrete consumers pass strict checks, with all 41 owned
declarations audited. The consumers use actual full-coefficient old
representables and both moving parities. Their identity-kernel tensor
contains an odd coefficient and mixed crossing and is proved nonzero at
every sufficiently large cutoff; a nonidentity negative-identity kernel
map is checked as even. The Hom-kernel comparison's actual grading is
discharged in [InductionKernelGrading](InductionKernelGrading.md).

Full CI is required before integration. Actual Ind–Res kernel grading,
finite sums and the prescribed matrix attachment remain separate;
see [STATUS](STATUS.md).
