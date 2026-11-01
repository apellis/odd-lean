# Canonically transported same-colour crossing tensors

`ELVInductionCrossTensor` proves the generator formula for a homogeneous transformation of a double functor conjugated by the existing canonical `BalancedInduction.inductionComp`. Both comparison directions are the previously constructed canonical isomorphism; no chosen comparison premise is introduced.

`ELVOldMateTensors.equalCrossOnDoubleInduction_total_tensor` specializes this formula to the actual full-coefficient equal-colour crossing. `signedEqualInductionCross_total_tensor` retains the prescribed extra minus. The statement holds for every moving colour, arbitrary old supermodule, and arbitrary balanced tensor factors. The full parity twist acts on the entire ordered morphism.

Verification: both producers and their closed mixed-parity consumers passed strict local Lean checks with the pinned toolchain and repository compatibility settings. The consumers audit every owned declaration (12 generic and 4 specialized declarations, including private/generated). Full branch CI is required before integration.

Remaining scope: evaluating the actual cup-crossing-cap mate, identifying its representable component with the fixed first row minus the cyclotomic crossing after canonical J, and attaching that equality to the previously constructed ordinary-source matrices. This note does not assert those identifications, the finite shifted-family inverse, content/truncation transport, or the completed action.
