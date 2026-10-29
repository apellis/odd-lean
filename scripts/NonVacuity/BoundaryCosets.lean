import OddMath.QuiverHecke.CyclotomicAction.BoundaryCosets
import Mathlib.Algebra.Group.PUnit

/-! Non-vacuity checks in `NonVacuity.BoundaryCosets`.
Conventions are in `scripts/NonVacuity.lean`. -/

noncomputable section

namespace NonVacuity.BoundaryCosets
open OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

/-- The short-coset boundary of a free polynomial module: `L₁ = L₀ = ℚ[t]`, no crossing
summand, `L₁' = 0`, `P` and `ℓ` the identity, `ρ = R_t` the dot. -/
def M : MackeyCosets (RingHom.id ℚ) (ℕ →₀ ℚ) (ℕ →₀ ℚ) Unit where
  P := AddMonoidHom.id _
  ρ := tShift (RingHom.id ℚ)
  Rt := tShift (RingHom.id ℚ)
  F := 0
  j := AddMonoidHom.id _
  X := 0
  E := 0
  short := ⊥
  ℓ := AddMonoidHom.id _
  r₁ := rsmul
  r₀ := rsmul
  P_ρ _ := rfl
  Rt_F _ := by simp
  Rt_j _ := rfl
  direct u f h := ⟨rfl, by simpa using h⟩
  span y := ⟨(), y, by simp⟩
  ρ_short z hz := by simp_all
  P_short z hz := ⟨(), by simp_all⟩
  cover z := ⟨z, by simp⟩
  ℓ_short v hv := by simpa using hv
  ρ_ℓ v := by simp
  ℓ_r b v := by simp
  P_r _ _ := rfl
  F_r _ _ := ⟨(), by simp⟩
  j_r _ _ := rfl

theorem monic_t : MonicDeg (Finsupp.single 1 (1 : ℚ)) 1 :=
  ⟨by simp, fun l hl => by simp [Finsupp.single_apply]; omega⟩

/-- Display (2) with `S = F = t` (`a = 0`), the lift of `t` given modulo `L₁' = 0`. -/
example (p : ℕ →₀ ℚ) : ∃! wr : (ℕ →₀ ℚ) × (ℕ →₀ ℚ), DegLT wr.2 (1 - 1) ∧ M.A wr.1 + wr.2 = p :=
  M.window_pos_of_short Function.injective_id monic_t monic_t (fun _ => rfl) 1 rfl
    (z₀ := Finsupp.single 1 1) (by simp [M]) (by ext; simp [M, lsmul]) le_rfl p

end NonVacuity.BoundaryCosets
