/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PolynomialExchange
import Mathlib.Data.ZMod.Basic

/-! # Concrete mixed-parity signed exchanges

Consumers of HW arXiv:1202.2769v2, Proposition 4.5, (4.22), including the
sign on an odd variable outside the exchanged pair and characteristic two.
-/

noncomputable section
namespace OddMath.QuiverHecke.Polynomial.ExchangeExamples

/-- Two adjacent odd positions, a distant even position and a distant odd position. -/
def mixed : Fin 4 → Bool := ![true, true, false, true]

/-- Odd–odd exchange negates the distant odd variable. -/
theorem distant_odd : exchange (R := ℤ) mixed 0 1 (X mixed 3) =
    -X (exchangeParity mixed 0 1) 3 := by
  simp [mixed, Equiv.swap_apply_def]

/-- The same exchange fixes the distant even variable. -/
theorem distant_even : exchange (R := ℤ) mixed 0 1 (X mixed 2) =
    X (exchangeParity mixed 0 1) 2 := by
  simp [mixed, Equiv.swap_apply_def]

/-- Mixed adjacent parities exchange without a generator sign. -/
theorem even_odd : exchange (R := ℤ) ![false, true] 0 1 (X ![false, true] 0) =
    X (exchangeParity ![false, true] 0 1) 1 := by
  simp

/-- Multiplicativity is checked on an inhomogeneous input with both parities. -/
theorem mixed_product (f : Polynomial ℤ 4 mixed) :
    exchange mixed 0 1 ((X mixed 2 + X mixed 3) * f) =
      exchange mixed 0 1 (X mixed 2 + X mixed 3) * exchange mixed 0 1 f :=
  exchange_mul mixed 0 1 (by decide) _ f

/-- The algebra equivalence has no characteristic restriction. -/
def characteristicTwo : Polynomial (ZMod 2) 4 mixed ≃ₐ[ZMod 2]
    Polynomial (ZMod 2) 4 (exchangeParity mixed 0 1) :=
  exchangeAlgEquiv mixed 0 1 (by decide)

/-- Characteristic two does not turn a square into an exterior zero. -/
theorem characteristicTwo_square : characteristicTwo (X mixed 3 ^ 2) ≠ 0 := by
  exact characteristicTwo.injective.ne (X_sq_ne_zero mixed 3) |>.trans_eq (map_zero _)

/-- The left and right distant exchanges on four odd positions. -/
def oddLeft : Module.End ℚ (Polynomial ℚ 4 (fun _ => true)) :=
  exchange (fun _ => true) 0 1

def oddRight : Module.End ℚ (Polynomial ℚ 4 (fun _ => true)) :=
  exchange (fun _ => true) 2 3

@[simp] theorem oddLeft_one : oddLeft 1 = 1 := exchange_one _ _ _
@[simp] theorem oddRight_one : oddRight 1 = 1 := exchange_one _ _ _

/-- These unital exchanges cannot be the odd distant crossings: the latter
must anticommute. This detects the obstruction in the unweighted specialization
of the printed HW Proposition 4.5 formula with two distinct odd colours. -/
theorem distant_not_anticommute : oddLeft * oddRight ≠ -(oddRight * oddLeft) := by
  intro h
  have h1 : (1 : Polynomial ℚ 4 (fun _ => true)) = -1 := by
    simpa only [Module.End.mul_apply, LinearMap.neg_apply, oddLeft_one, oddRight_one] using
      congrArg (fun T : Module.End ℚ (Polynomial ℚ 4 (fun _ => true)) => T 1) h
  have hc := congrArg (fun f : Polynomial ℚ 4 (fun _ => true) => (show (Fin 4 → ℕ) →₀ ℚ from f) 0) h1
  change (Finsupp.single (0 : Fin 4 → ℕ) (1 : ℚ)) 0 =
    (-Finsupp.single (0 : Fin 4 → ℕ) (1 : ℚ)) 0 at hc
  norm_num at hc

#print axioms distant_not_anticommute
#print axioms exchangeSign_cocycle
#print axioms exchangeAlgEquiv
#print axioms exchange_X_mul
#print axioms distant_odd
#print axioms characteristicTwo_square

end OddMath.QuiverHecke.Polynomial.ExchangeExamples
