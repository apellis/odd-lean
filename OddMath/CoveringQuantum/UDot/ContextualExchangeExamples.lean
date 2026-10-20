/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.ContextualExchange

/-! Two odd colours in nonempty mixed context for BE2 Theorem 10.3 Claim 4. -/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open Coefficients GenericTensor GenericVerma.MixedGram

/-- Two orthogonal odd roots, with the coordinate weight realization. -/
def twoOddDatum : RootDatum Bool (Bool → ℤ) where
  a := Matrix.of fun i j => if i = j then 2 else 0
  isGCM :=
    { diag := fun _ => by simp
      offDiag_nonpos := fun _ _ h => by simp [h]
      zero_comm := fun _ _ => by simp [eq_comm] }
  d := fun _ => 1
  d_pos := fun _ => one_pos
  d_mul_symm := fun _ _ => by simp [eq_comm]
  parity := fun _ => 1
  even_of_odd := fun i j _ => by by_cases h : i = j <;> simp [h]
  cd :=
    { root := fun i j => if i = j then 2 else 0
      coroot := fun i =>
        { toFun := fun μ => μ i
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      coroot_root_self := fun _ => by simp }
  coroot_root i j := by simp [eq_comm]

theorem twoOdd_barConsistent : twoOddDatum.toSuperCartanDatum.BarConsistent := fun _ => rfl

/-- Nonempty prefix and suffix, both odd colours, in the actual generic coefficient ring. -/
theorem twoOdd_context_exchange :
    sesquilinearForm twoOddDatum
      (algebraWord twoOddDatum 0 [(false, false), (true, false), (false, true), (true, true)])
      (algebraWord twoOddDatum 0 []) =
    pi * sesquilinearForm twoOddDatum
      (algebraWord twoOddDatum 0 [(false, false), (false, true), (true, false), (true, true)])
      (algebraWord twoOddDatum 0 []) := by
  have h := sesquilinearForm_context_EF_ne twoOddDatum 0
    [(false, false)] [(true, true)] false true (by decide)
  simpa only [twoOddDatum, one_mul, ZMod.val_one, pow_one, List.cons_append,
    List.nil_append] using h

/-- The same nonempty consumer gives opposite signs in the two π specializations. -/
theorem twoOdd_context_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm twoOddDatum
      (algebraWord twoOddDatum 0 [(false, false), (true, false), (false, true), (true, true)])
      (algebraWord twoOddDatum 0 []))).coeff z =
    σ * (signLaurent σ hσ (sesquilinearForm twoOddDatum
      (algebraWord twoOddDatum 0 [(false, false), (false, true), (true, false), (true, true)])
      (algebraWord twoOddDatum 0 []))).coeff z := by
  have h := sesquilinearForm_context_EF_ne_coeff twoOddDatum σ hσ 0
    [(false, false)] [(true, true)] false true (by decide) z
  simpa only [twoOddDatum, one_mul, ZMod.val_one, pow_one, List.cons_append,
    List.nil_append] using h

end OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
