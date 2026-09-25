import OddMath.Frontier.CompleteElementary

/-! Universal free-algebra change of generators corresponding to
Ellis–Khovanov 1107.5610v2 §2.2 (2.5)–(2.6).
No quotient descent, reversed convolution, or involutivity is assumed. -/
namespace OddMath.Frontier.CompleteChangeOfGenerators

open CompleteElementary
open scoped BigOperators

/-- Recover complete letters from raw elementary letters, in the same free algebra. -/
def recoveredComplete : ℕ → A
  | 0 => 1
  | n + 1 => - ∑ j : Fin (n + 1),
      ekSign (j + 1) * h (j + 1) * recoveredComplete (n - j)
termination_by n => n

@[simp] theorem recoveredComplete_zero : recoveredComplete 0 = 1 := by
  simp [recoveredComplete]

/-- Substitute the actual elementary polynomials for the free generators. -/
def completeToElementary : A →ₐ[ℤ] A :=
  FreeAlgebra.lift ℤ (fun i => elementary (i + 1))

/-- The explicitly recursive inverse substitution. -/
def elementaryToComplete : A →ₐ[ℤ] A :=
  FreeAlgebra.lift ℤ (fun i => recoveredComplete (i + 1))

@[simp] theorem completeToElementary_h (n : ℕ) :
    completeToElementary (h n) = elementary n := by
  cases n with
  | zero => simp
  | succ n => exact FreeAlgebra.lift_ι_apply _ n

@[simp] theorem elementaryToComplete_h (n : ℕ) :
    elementaryToComplete (h n) = recoveredComplete n := by
  cases n with
  | zero => simp
  | succ n => exact FreeAlgebra.lift_ι_apply _ n

@[simp] theorem map_ekSign (f : A →ₐ[ℤ] A) (n : ℕ) :
    f (ekSign n) = ekSign n := by
  simp [ekSign]

/-- Isolate the zeroth term of the given e*h identity; no order reversal. -/
theorem h_succ (n : ℕ) :
    h (n + 1) = - ∑ j : Fin (n + 1),
      ekSign (j + 1) * elementary (j + 1) * h (n - j) := by
  have hh := elementary_complete_inverse n
  rw [Fin.sum_univ_succ] at hh
  simp only [Fin.val_zero, ekSign, Nat.zero_add, Nat.choose_eq_zero_of_lt (by decide : 1 < 2),
    pow_zero, elementary_zero, one_mul, Nat.sub_zero, Fin.val_succ] at hh
  simpa only [Nat.add_sub_add_right] using eq_neg_of_add_eq_zero_left hh

/-- The defining recovered sequence satisfies the same ordered convolution. -/
theorem recovered_convolution (n : ℕ) :
    ∑ k : Fin (n + 2), ekSign k * h k * recoveredComplete (n + 1 - k) = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, h_zero, ekSign, Nat.zero_add,
    Nat.choose_eq_zero_of_lt (by decide : 1 < 2), pow_zero, one_mul, Nat.sub_zero,
    Fin.val_succ, Nat.add_sub_add_right]
  rw [recoveredComplete]
  exact neg_add_cancel _

/-- The forward substitution recovers every complete generator, including degree zero. -/
theorem completeToElementary_recoveredComplete (n : ℕ) :
    completeToElementary (recoveredComplete n) = h n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [recoveredComplete, map_neg, map_sum, h_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [map_mul, map_ekSign, completeToElementary_h]
      rw [ih (n - j) (by omega)]

/-- Uniqueness of left coefficients for an ordered convolution, with right constant 1.
Works in every ring, with no commutativity or inverse hypotheses. -/
theorem ordered_convolution_unique {R : Type*} [Ring R]
    (f g r : ℕ → R) (hr : r 0 = 1) (hzero : f 0 = g 0)
    (hf : ∀ n, ∑ k : Fin (n + 2), f k * r (n + 1 - k) = 0)
    (hg : ∀ n, ∑ k : Fin (n + 2), g k * r (n + 1 - k) = 0) :
    ∀ n, f n = g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hzero
    | succ n =>
      have hf' := hf n
      have hg' := hg n
      rw [Fin.sum_univ_castSucc] at hf' hg'
      simp only [Fin.coe_castSucc, Fin.val_last, Nat.sub_self, hr, mul_one] at hf' hg'
      have hs : (∑ k : Fin (n + 1), f k * r (n + 1 - k)) =
          ∑ k : Fin (n + 1), g k * r (n + 1 - k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [ih k k.isLt]
      rw [hs] at hf'
      exact add_left_cancel (hf'.trans hg'.symm)

/-- The inverse substitution recovers all elementary generators. -/
theorem elementaryToComplete_elementary (n : ℕ) :
    elementaryToComplete (elementary n) = h n := by
  have heq := ordered_convolution_unique
    (fun k => ekSign k * elementaryToComplete (elementary k))
    (fun k => ekSign k * h k) recoveredComplete recoveredComplete_zero
    (by simp)
    (fun m => by
      have hh := congrArg elementaryToComplete (elementary_complete_inverse m)
      simpa only [map_sum, map_mul, map_ekSign, elementaryToComplete_h, map_zero] using hh)
    recovered_convolution n
  have hh := congrArg (fun x => ekSign n * x) heq
  simpa only [← mul_assoc, ekSign_sq, one_mul] using hh

/-- Forward after inverse is the identity on arbitrary free-algebra elements. -/
theorem completeToElementary_comp_elementaryToComplete :
    completeToElementary.comp elementaryToComplete = AlgHom.id ℤ A := by
  apply FreeAlgebra.hom_ext
  funext i
  change completeToElementary (elementaryToComplete (h (i + 1))) = h (i + 1)
  rw [elementaryToComplete_h, completeToElementary_recoveredComplete]

/-- Inverse after forward is the identity on arbitrary free-algebra elements. -/
theorem elementaryToComplete_comp_completeToElementary :
    elementaryToComplete.comp completeToElementary = AlgHom.id ℤ A := by
  apply FreeAlgebra.hom_ext
  funext i
  change elementaryToComplete (completeToElementary (h (i + 1))) = h (i + 1)
  rw [completeToElementary_h, elementaryToComplete_elementary]

/-- The universal complete-to-elementary change of generators, not an involution. -/
def completeElementaryEquiv : A ≃ₐ[ℤ] A :=
  AlgEquiv.ofAlgHom completeToElementary elementaryToComplete
    completeToElementary_comp_elementaryToComplete
    elementaryToComplete_comp_completeToElementary

end OddMath.Frontier.CompleteChangeOfGenerators
