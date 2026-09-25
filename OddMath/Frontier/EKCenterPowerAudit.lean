import OddMath.Frontier.EKCenterPower

/-! Audit for `EKCenterPower`: statement pin (with `p k` unfolded to the
integral dual basis element `m_(k)`) and axiom report. -/
namespace OddMath.Frontier.EKCenterPowerAudit
open OddMath.Frontier EKCenterPower EKRadicalQuotient

/-- Pinned statement: for every `k ≥ 1`, `m_(k) := (mBasis k (k)).val` is central in
the actual quotient `Q` iff `k` is even. -/
example (k : ℕ) (hk : 1 ≤ k) :
    (∀ y : Q, (EKDualBases.mBasis k (rowShape k)).val * y =
      y * (EKDualBases.mBasis k (rowShape k)).val) ↔ Even k :=
  center_iff k hk

/-- `rowShape k` really is the one-row diagram `(k)`. -/
example (k : ℕ) (hk : 0 < k) : (rowShape k).val.rowLens = [k] := rowShape_rows k hk

/-- Odd witness structure: `k = 1` via `h_2` (control); odd `k ≥ 3` via `h_1`. -/
example : EKCenterPower.p 3 * EKElementaryQuotient.h 1 ≠ EKElementaryQuotient.h 1 * EKCenterPower.p 3 :=
  not_central_odd 3 le_rfl ⟨1, rfl⟩

#print axioms center_iff
#print axioms central_of_even
#print axioms not_central_odd
#print axioms EKCenterPowerControls.control_k1
#print axioms EKCenterPowerControls.control_k2

end OddMath.Frontier.EKCenterPowerAudit
