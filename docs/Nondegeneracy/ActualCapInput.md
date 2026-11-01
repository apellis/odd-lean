# Actual cap and input dot on arbitrary old Hom endpoints

Status: production and paired asymmetric consumer passed strict local Lean checks (including the all-owned-declaration axiom audit); full CI pending.

ELVOldAppendDot constructs the old append dot from the full-coefficient appended component and proves its supernaturality. ELVActualCapInput defines contraction from the constructed shifted counit followed by total output parity, and input dot from the constructed induction dot composed with shifted-source grading. The coefficient(1) shift contributes the tensor minus. The full-coefficient contraction, grading and input-dot formulas hold at arbitrary old endpoints over an arbitrary commutative base ring.

The literal Source comes from inducing movingCoefficientModule, which packages coefficient(D.parity j) before forming its coend. Its even pointwise coefficient comparison is induced to construct coefficientOneSourceEquiv. No equality recursor transports an entire coend. The source-sign proof uses the standard balanced-tensor grading identity, checked abstractly before its coefficient specialization.

Remaining categorical consumers: agreement with the checked raw input operators, higher dotted-counit normalization, the prescribed crossing/mate and cup-column comparison, and action-level natural isomorphisms after homogeneous coefficient truncation and exact-content transport. Arbitrary-endpoint boundary leading/division are handled in their own modules; no diagonal-to-arbitrary inverse inference is made here.
