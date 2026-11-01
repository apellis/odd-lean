# Actual signed crossing mate on old balanced generators

`ELVOldMateEvaluation.oldModuleMate_total_tensor` evaluates the fixed `oldModuleMate`, constructed from the actual induction/restriction adjunction and prescribed signed equal-colour double crossing. For every moving colour, old supermodule N and generator [g tensor b], its parity-square component is minus [cross_s composed with twist_(parity i squared)(append(g)) tensor b]. The twist acts on the entire ordered old morphism, including homogeneous coefficients.

The proof specializes `ELVInductionMateTensor.orderedMateComponent_total_tensor`, whose map is literally the existing unit, restricted signed canonical crossing and restricted induced counit, in that order. No mate/component equality premise, determinant, field, flatness or finite-colour premise is introduced.

Strict local producers and both concrete mixed-parity consumers passed; every owned declaration was audited (17 generic and 4 actual, including private/generated). Full branch CI remains required before research integration.

Remaining scope: the representable co-Yoneda evaluation and canonical J generator calculation must identify this actual mate with the fixed first row minus the cyclotomic crossing after J. The finite-family inverse and content/weighted-quotient transports are separate subsequent attachments. This result alone does not assert the completed categorical matrix or action.
