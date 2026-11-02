# Target naturality of the induction-restriction kernel

Current scope and verification are maintained in [STATUS](STATUS.md). Any original
topic-head pending checks below are historical; they do not override the consolidated
status or establish completion of the full conjecture.

The quotient equivalence in [IndResKernel](IndResKernel.md) must intertwine actual target morphisms to serve the kernel comparison in [DeformedMatrixComparison](DeformedMatrixComparison.md), section 4.

The proposed ELVIndResKernelNaturality constructs IndResKernel.targetMap by postcomposition on the outer induction arrow. It commutes with ordinary-right source precomposition, so IndResKernel.kernelFunctor is a target-covariant family of source presheaves. The forward evaluation and backward identity insertion intertwine this action by forward_targetMap and backward_postcompose. The coefficient tensor quotients carry the resulting tensorFunctor action.

The producer and concrete old-quotient consumer passed strict local checking, including the audit of every owned declaration. Repository CI remains the integration gate. These statements concern all ordinary underlying target arrows, with no parity restriction on their components. Grading transport and identification with the prescribed categorical matrix remain separate.
