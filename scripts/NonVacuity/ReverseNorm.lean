import OddMath.QuiverHecke.CyclotomicAction.ReverseNorm
import Mathlib.Algebra.Polynomial.Basic

/-! Non-vacuity checks in `NonVacuity.ReverseNorm`.
Conventions are in `scripts/NonVacuity.lean`. -/

namespace NonVacuity.ReverseNorm
open OddMath.QuiverHecke.CyclotomicAction.ReverseNorm

/-- Leading-term injectivity for the identity map (`d = 0`, `c = id`). -/
example : Function.Injective (AddMonoidHom.id (ℕ →₀ ℤ)) :=
  injective_of_leading _ 0 (AddMonoidHom.id ℤ) Function.injective_id
    fun _ _ h => ⟨fun l hl => h l (by omega), rfl⟩

/-- The reverse norm identity in `ℚ[X]` with `J_L = J_R = 0`, `G = G' = X`, `f = f' = X + 1`,
`ε = 1`, `T = 1`, `L = L_left = X`. -/
example : (Polynomial.X : Polynomial ℚ) * (Polynomial.X + 1) * 1 -
    1 * (Polynomial.X + 1) * Polynomial.X ∈ (⊥ : Submodule (Polynomial ℚ) (Polynomial ℚ)) :=
  reverse_norm ⊥ ⊥ (G' := Polynomial.X) (Lleft := Polynomial.X)
    (fun h hh => by
      rw [Submodule.mem_bot] at hh ⊢
      exact (mul_eq_zero.mp hh).resolve_right
        (mul_ne_zero Polynomial.X_ne_zero Polynomial.X_ne_zero))
    (fun h hh => by rw [Submodule.mem_bot] at hh ⊢; rw [hh, zero_mul])
    (by rw [Submodule.mem_bot]; ring) (by ring) rfl

end NonVacuity.ReverseNorm
