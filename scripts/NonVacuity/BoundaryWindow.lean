import OddMath.QuiverHecke.CyclotomicAction.BoundaryWindow

/-! Non-vacuity checks in `NonVacuity.BoundaryWindow`.
Conventions are in `scripts/NonVacuity.lean`. -/

noncomputable section

namespace NonVacuity.BoundaryWindow
open OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

/-- `φ_k = t^(a+k)` over `ℚ`, leading coefficient `1`. -/
theorem leadsAt_pow (a : ℕ) : LeadsAt (fun k => Finsupp.single (a + k) (1 : ℚ)) 1 a :=
  fun k => ⟨by simp, fun l hl => by simp [Finsupp.single_apply]; omega⟩

/-- `a = 2`: every polynomial is uniquely `A_∂ w + r` with `deg r < 2`. -/
example (p : ℕ →₀ ℚ) : ∃! wr : (ℕ →₀ ℚ) × (ℕ →₀ ℚ),
    DegLT wr.2 2 ∧ windowMap (fun k => Finsupp.single (2 + k) (1 : ℚ)) wr.1 + wr.2 = p :=
  windowMap_add_low_existsUnique isUnit_one (leadsAt_pow 2) p

/-- `a = −1`: `φ_0 = 0`, `φ_(1+j) = t^j`, `σ = id`. -/
abbrev φneg (k : ℕ) : ℕ →₀ ℚ := if k = 0 then 0 else Finsupp.single (k - 1) 1

theorem φneg_zero : ∀ k < 1, φneg k = 0 := fun k hk => by simp [φneg, show k = 0 by omega]

theorem φneg_leads : LeadsAt (fun j => φneg (1 + j)) 1 0 := by
  intro k
  simp only [φneg, show 1 + k ≠ 0 by omega, ite_false, show 1 + k - 1 = k by omega]
  exact leadsAt_pow 0 k |>.imp (by simp) (by simp)

example (p : ℕ →₀ ℚ) (x : ℕ → ℚ) : ∃! v : ℕ →₀ ℚ,
    windowMap φneg v = p ∧ ∀ r < 1, capRow (RingHom.id ℚ) φneg r v = x r :=
  windowMap_cap_existsUnique (RingHom.id ℚ) Function.bijective_id isUnit_one φneg_zero
    φneg_leads p x

example (w : ℕ →₀ ℚ) : windowMap φneg w = 0 ↔ DegLT w 1 :=
  windowMap_eq_zero_iff isUnit_one φneg_zero φneg_leads w

end NonVacuity.BoundaryWindow
