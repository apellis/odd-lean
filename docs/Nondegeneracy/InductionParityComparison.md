# Canonical induction parity and counit comparison

Status: proposed Lean implementation; full CI pending. Target: DeformedMatrixComparison (3), (5).

ELVContentParity supplies actual module parity from SVec. ELVInductionParityComparison maps that canonical isomorphism through actual restriction and balanced induction, computes each coend-generator component with total kernel twist, and compares whole actual counits by naturality. ELVOldSupermodules uses the existing old quotient parity decomposition to construct its supercategory and actual covariant representables.

Remaining: identify the prescribed coefficient(1) module with parity-shifted restriction representable; transport to coefficient-truncated exact content; compare actual dotted counits with input contraction rows. No arbitrary kernel isomorphism, factor action or nondegeneracy theorem is asserted.
