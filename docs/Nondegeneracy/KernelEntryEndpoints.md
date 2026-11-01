# Module endpoints of the mate evaluation

The whole finite matrix comparison in [DeformedMatrixComparison](DeformedMatrixComparison.md), section 4, needs the two mate evaluations to have the same literal module target before they are applied.

ELVKernelEntryEndpoints retains the existing coefficient equality from KernelEntryEvaluation. Both kernelMateEvaluationEndpoint and moduleMateEvaluationEndpoint target mateTargetSpace, the actual restriction-induction module on M. The prescribed mate itself is named moduleMateLinear with literal induction-restriction source and restriction-induction target. The coefficient insertion is named mateCoefficientEvaluation with the same target, and mateSourceEvaluation fixes its matching source-module dictionary before composition.

The endpoint equality follows on pure tensors from the established coefficient comparison. Getter identities apply only named linear maps; total mate evaluation is exposed afterward in moduleMateLinear_apply. This does not introduce another mate, change the kernel map, or alter the old quotient presentation.

The producer and concrete old-quotient consumer passed strict local checking, including the audit of every owned declaration. Repository CI remains the integration gate. These are endpoint comparisons needed by the whole prescribed forward matrix identity; arbitrary-module inversion remains separate.
