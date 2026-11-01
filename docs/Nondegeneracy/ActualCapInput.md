# Actual cap and input dot on arbitrary old Hom endpoints

Status: proposed Lean source and consumers, unchecked pending CI and upstream actual module stack.

ELVOldAppendDot constructs the actual old append dot using the existing full-coefficient appended component and proves its supernaturality. ELVActualCapInput defines contraction from the actual shifted counit followed by total output parity, and input dot from the actual induction dot composed with actual shifted source grading. Actual coefficient(1) shifts the source grading: its tensor formula carries an extra minus. It proves the full-coefficient contraction and input-dot tensor formulas with arbitrary old endpoints, and defines the corresponding maps on the literal Source via coefficientOneSourceEquiv.

Remaining: source checks, agreement with diagonal raw input-defect maps, higher dotted-counit normalization, arbitrary-endpoint boundary leading/division, and action-level natural isomorphisms. No diagonal-to-arbitrary inverse inference is made.

Includes known upstream canonical parity-instance and consumer-namespace repairs locally, preserving #769's first diagnostics run.
