import OddMath.QuiverHecke.CyclotomicAction.BoundaryAssembly
import Mathlib.Algebra.Group.PUnit

/-! Non-vacuity checks in `NonVacuity.BoundaryAssembly`.
Conventions are in `scripts/NonVacuity.lean`. -/

noncomputable section

namespace NonVacuity.BoundaryAssembly
open OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

/-- The boundary of a free polynomial module: `L₁ = L₀ = ℚ[t]`, no crossing summand,
`P`, `B₁` and `A_∂` the identity, `ρ = R_t` the dot. -/
def M : MackeyBoundary (RingHom.id ℚ) (ℕ →₀ ℚ) (ℕ →₀ ℚ) Unit where
  P := AddMonoidHom.id _
  ρ := tShift (RingHom.id ℚ)
  Rt := tShift (RingHom.id ℚ)
  F := 0
  j := AddMonoidHom.id _
  X := 0
  E := 0
  B₁ := AddMonoidHom.id _
  A := AddMonoidHom.id _
  P_ρ _ := rfl
  Rt_F _ := by simp
  Rt_j _ := rfl
  direct u f h := ⟨rfl, by simpa using h⟩
  B₁_ρ _ := rfl
  B₁_surjective := Function.surjective_id
  P_split z := ⟨(), by simp⟩
  A_rsmul _ _ := rfl

theorem monic_t : MonicDeg (Finsupp.single 1 (1 : ℚ)) 1 :=
  ⟨by simp, fun l hl => by simp [Finsupp.single_apply]; omega⟩

/-- Display (2) with `S = F = t` (`a = 0`): `A_∂` is bijective. -/
example (p : ℕ →₀ ℚ) : ∃! wr : (ℕ →₀ ℚ) × (ℕ →₀ ℚ), DegLT wr.2 (1 - 1) ∧ M.A wr.1 + wr.2 = p :=
  M.window_pos Function.injective_id monic_t monic_t (fun _ => rfl) 1 rfl
    (z₀ := Finsupp.single 1 1) rfl (by ext; simp [M, lsmul]) le_rfl p

end NonVacuity.BoundaryAssembly
