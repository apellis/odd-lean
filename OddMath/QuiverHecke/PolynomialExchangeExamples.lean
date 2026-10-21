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

#print axioms exchangeSign_cocycle
#print axioms exchangeAlgEquiv
#print axioms exchange_X_mul
#print axioms distant_odd
#print axioms characteristicTwo_square

end OddMath.QuiverHecke.Polynomial.ExchangeExamples
