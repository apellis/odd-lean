import OddMath.Algebra.FrobeniusResolvent
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! A repeated-root probe: y = 1 + ε in Q[ε]/ε², with characteristic
polynomial (Y-1)². This checks the resolvent theorem without simple roots. -/

open OddMath.FrobeniusResolvent

namespace FrobeniusResolventExample

abbrev A := TrivSqZeroExt ℚ ℚ

def y : A := ⟨1, 1⟩
def r : A := ⟨-1, 1⟩
def c : Fin 2 → ℚ := ![1, -2]
def τ : A →ₗ[ℚ] ℚ := TrivSqZeroExt.sndHom ℚ ℚ

example : y ^ 2 + ∑ k : Fin 2, c k • y ^ (k : ℕ) = 0 := by
  ext <;> norm_num [y, c, pow_two, Fin.sum_univ_two, TrivSqZeroExt.snd_mul]

example : (algebraMap ℚ A 0 - y) * r = 1 := by
  ext <;> norm_num [y, r, TrivSqZeroExt.snd_mul]

example : ∀ k < 2, τ (y ^ k) = if k + 1 = 2 then 1 else 0 := by
  intro k hk
  interval_cases k <;> norm_num [τ, y, TrivSqZeroExt.sndHom]

example (j : ℕ) (hj : j < 2) :
    ((0 : ℚ) ^ 2 + ∑ k : Fin 2, c k * 0 ^ (k : ℕ)) * τ (y ^ j * r) = 0 ^ j := by
  apply characteristic_mul_moment τ y r 0 2 (by decide) c _ _ _ j hj
  · ext <;> norm_num [y, c, pow_two, Fin.sum_univ_two, TrivSqZeroExt.snd_mul]
  · ext <;> norm_num [y, r, TrivSqZeroExt.snd_mul]
  · intro k hk
    interval_cases k <;> norm_num [τ, y, TrivSqZeroExt.sndHom]

#print axioms OddMath.FrobeniusResolvent.characteristic_mul_trace
#print axioms OddMath.FrobeniusResolvent.characteristic_mul_moment

end FrobeniusResolventExample
