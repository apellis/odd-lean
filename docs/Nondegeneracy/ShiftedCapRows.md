# Prescribed higher cap-row normalization

Status: producer and paired asymmetric consumer passed strict local Lean checks, including the all-owned-declaration axiom audit. Full CI pending. Target: DeformedMatrixComparison (5).

ELVShiftedCapRows proves shiftedCapRow_normalization for every odd moving colour, arbitrary old source and target words, and every dot exponent n. The maps are the constructed induction dot, the actual adjunction counit and the canonical source-parity isomorphism. The row is exactly capRowSign(n) times the whole output twist of parity n+1 applied to E X^n J; capRowSign(n)=(-1)^(n(n+1)/2). No chosen-J or presumed matrix-row equality is supplied.

ELVCapSignNormalization supplies the checked abstract sign calculation; ELVActualCapParity supplies parity and anticommutation of the fixed module maps. Combining these rows with the checked raw matrix still requires its separate component comparison and the prescribed categorical crossing/mate and cup columns. The result is on old/untruncated representables; homogeneous coefficient truncation, exact-content/global transport and a complete action are separate work.
