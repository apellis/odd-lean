import OddMath.CoveringQuantum.Integers
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Group

/-!
# Twisting quantum binomial coefficients

Multiplying the quantum parameter by a fourth root of unity exchanges the
ordinary and covering binomials, with an explicit scalar phase. This identity
is needed to compare the Serre generators under the ordered word map.
-/

namespace OddMath.CoveringQuantum

variable {k : Type*} [CommRing k] (q u : kˣ) (hu : u ^ 4 = 1)

include hu

private theorem phase_eq {a b : ℤ} (h : Int.ModEq 4 a b) : u ^ a = u ^ b := by
  calc
    _ = u ^ (a % 4) := zpow_eq_zpow_emod' a hu
    _ = u ^ (b % 4) := congrArg (fun n : ℤ ↦ u ^ n) h
    _ = _ := (zpow_eq_zpow_emod' b hu).symm

/-- The binomial phase under a fourth-root parameter twist; the exponent is integral
so the formula also applies to the zero coefficients outside the binomial range. -/
theorem qpBinom_twist (n r : ℕ) :
    qpBinom (u * q) 1 n r =
      ((u ^ ((r : ℤ) * ((n : ℤ) - r)) : kˣ) : k) * qpBinom q ((u : k) ^ 2) n r := by
  induction n generalizing r with
  | zero => cases r <;> simp [qpBinom]
  | succ n ih =>
    cases r with
    | zero => simp
    | succ r =>
      by_cases hr : r < n
      · have h1 : (u * q) ^ (-(r + 1 : ℤ)) * u ^ ((r + 1 : ℤ) * ((n : ℤ) - (r + 1))) =
            u ^ ((r + 1 : ℤ) * ((n + 1 : ℤ) - (r + 1))) *
              (u ^ 2) ^ (r + 1) * q ^ (-(r + 1 : ℤ)) := by
          have hp : u ^ (-(r + 1 : ℤ) + (r + 1 : ℤ) * ((n : ℤ) - (r + 1))) =
              u ^ ((r + 1 : ℤ) * ((n + 1 : ℤ) - (r + 1)) + 2 * (r + 1 : ℤ)) := by
            apply phase_eq u hu
            change _ % 4 = _ % 4
            ring_nf
            omega
          calc
            _ = u ^ (-(r + 1 : ℤ) + (r + 1 : ℤ) * ((n : ℤ) - (r + 1))) *
                q ^ (-(r + 1 : ℤ)) := by rw [mul_zpow, mul_right_comm, ← zpow_add]
            _ = _ := by rw [hp]; group
        have h2 : (u * q) ^ (n - r) * u ^ ((r : ℤ) * ((n : ℤ) - r)) =
            u ^ ((r + 1 : ℤ) * ((n + 1 : ℤ) - (r + 1))) * q ^ (n - r) := by
          rw [← zpow_natCast (u * q), ← zpow_natCast q, Nat.cast_sub hr.le]
          rw [mul_zpow, mul_right_comm, ← zpow_add]
          congr 2
          ring
        have hc1 := congrArg (fun v : kˣ ↦ (v : k)) h1
        have hc2 := congrArg (fun v : kˣ ↦ (v : k)) h2
        have he : (r : ℤ) + 1 = ((r + 1 : ℕ) : ℤ) := by push_cast; rfl
        simp only [he, zpow_neg, zpow_natCast, Units.val_mul,
          Units.val_pow_eq_pow_val] at hc1
        rw [← inv_pow, ← inv_pow] at hc1
        simp only [Nat.cast_add, Nat.cast_one, Units.val_pow_eq_pow_val] at hc1
        simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hc2
        rw [qpBinom_succ_succ, qpBinom_succ_succ, ih, ih]
        simp only [one_pow, one_mul, Nat.cast_add, Nat.cast_one, Units.val_mul]
        linear_combination
          hc1 * qpBinom q ((u : k) ^ 2) n (r + 1) +
          hc2 * qpBinom q ((u : k) ^ 2) n r
      · by_cases heq : r = n
        · subst r
          simp only [qpBinom_self, Nat.cast_add, Nat.cast_one, sub_self, mul_zero,
            zpow_zero, Units.val_one, one_mul]
        · have hnr : n + 1 < r + 1 := by omega
          rw [qpBinom_eq_zero_of_lt hnr, qpBinom_eq_zero_of_lt hnr, mul_zero]

end OddMath.CoveringQuantum
