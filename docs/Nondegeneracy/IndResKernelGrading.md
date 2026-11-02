# Grading of the induction-restriction coefficient kernel

Current scope and verification are maintained in [STATUS](STATUS.md). Any original
topic-head pending checks below are historical; they do not override the consolidated
status or establish completion of the full conjecture.

The kernel tensor transfer in [DeformedMatrixComparison](DeformedMatrixComparison.md), section 4, needs the grading of its ordinary-right coefficient kernels. The proposed ELVIndResKernelGrading supplies generic additive, linear and superfunctor instances for IndResKernel.homModule; its values retain the full Hom superspace.

The ordinary-right coefficient source presheaf is additive. IndResKernel.coefficientGrading uses the existing balanced-induction odd projector on U_t(v), with no replacement of its module or quotient. Its coefficientSpace is definitionally the existing BalancedInduction.superspace.

For a homogeneous source arrow a:u→v of degree p, precompose(a) sends [g tensor b] to [g tensor a b]. Its degree is p. The proof projects the second factor using the homogeneous composition projection law; at p=1 the two sum-grading terms exchange positions. The result is packaged as IndResKernel.isGradedKernel, the input required by the generic quotient grading.

Producer and concrete old-quotient consumer passed strict local checking, including the audit of every owned declaration. Repository CI remains the integration gate. These are grading prerequisites, not the complete evenness of the double-coend evaluation equivalence or the attachment of a prescribed categorical matrix. No exterior coefficient is discarded.
