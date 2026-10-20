/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.MatchingEndpointSupport
/-! # Contextual distinct-colour exchange

Algebraic adjacent exchange for BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 4.
The form uses additive weights and decidable equalities over the purely-even
generic covering coefficient ring, with arbitrary colours and no bar consistency. These identities
hold at every endpoint and do not assume a graphical comparison.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram
open Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

omit [DecidableEq I] [DecidableEq X] in
theorem shift_append (a b : List (Bool × I)) :
    shift D (a ++ b) = shift D a + shift D b := by
  induction a with
  | nil => simp [shift]
  | cons g a ih => simp only [List.cons_append, shift, ih, add_assoc]

/-- Concatenation is multiplication at the actual endpoint of the suffix. -/
theorem algebraWord_append (ζ : X) (a b : List (Bool × I)) :
    algebraWord D ζ (a ++ b) =
      algebraWord D (ζ + shift D b) a * algebraWord D ζ b := by
  induction a with
  | nil =>
    apply Subtype.ext
    exact (algebraWord_mem_block D ζ b).1.symm
  | cons g a ih =>
    simp only [List.cons_append, algebraWord, shift_append, ih, mul_assoc, add_assoc,
      add_comm (shift D a) (shift D b)]

/-- The defining mixed relation after an arbitrary suffix. -/
private theorem algebraWord_comm_suffix (ζ : X) (i j : I) (b : List (Bool × I)) :
    algebraWord D ζ ((true, i) :: (false, j) :: b) -
        pi ^ (D.parity i * D.parity j).val •
          algebraWord D ζ ((false, j) :: (true, i) :: b) =
      if i = j then qpInt (D.qi Coefficients.q i) (D.pii pi i)
        (D.h i (ζ + shift D b)) • algebraWord D ζ b else 0 := by
  apply Subtype.ext
  change E D Coefficients.q pi i (ζ + (-D.α j + shift D b)) *
      (F D Coefficients.q pi j (ζ + shift D b) * (algebraWord D ζ b).val) -
    pi ^ (D.parity i * D.parity j).val •
      (F D Coefficients.q pi j (ζ + (D.α i + shift D b)) *
        (E D Coefficients.q pi i (ζ + shift D b) * (algebraWord D ζ b).val)) = _
  rw [show ζ + (-D.α j + shift D b) = ζ + shift D b - D.α j by abel,
    show ζ + (D.α i + shift D b) = ζ + shift D b + D.α i by abel,
    ← mul_assoc, ← mul_assoc, ← smul_mul_assoc, ← sub_mul, comm_rel]
  split_ifs with h
  · change (qpInt _ _ _ • one D Coefficients.q pi (ζ + shift D b)) *
        (algebraWord D ζ b).val = _
    rw [smul_mul_assoc, (algebraWord_mem_block D ζ b).1]
    rfl
  · exact zero_mul _

/-- Distinct-colour exchange in arbitrary physical prefix/suffix context. -/
theorem algebraWord_context_EF_ne (ζ : X) (a b : List (Bool × I))
    (i j : I) (hij : i ≠ j) :
    algebraWord D ζ (a ++ (true, i) :: (false, j) :: b) =
      pi ^ (D.parity i * D.parity j).val •
        algebraWord D ζ (a ++ (false, j) :: (true, i) :: b) := by
  have h := algebraWord_comm_suffix D ζ i j b
  rw [ite_eq_right hij] at h
  have he : algebraWord D ζ ((true, i) :: (false, j) :: b) =
      pi ^ (D.parity i * D.parity j).val •
        algebraWord D ζ ((false, j) :: (true, i) :: b) := by
    apply Subtype.ext
    exact sub_eq_zero.mp (congrArg Subtype.val h)
  rw [algebraWord_append, algebraWord_append]
  have hs : shift D ((true, i) :: (false, j) :: b) =
      shift D ((false, j) :: (true, i) :: b) := by
    simp only [shift, halfRoot, ite_true, Bool.false_eq_true, ite_false]
    abel
  rw [hs, he, mul_smul_comm]


end OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram

namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients GenericVerma.MixedGram
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

/-- Algebraic adjacent exchange for Claim 4, with arbitrary mixed context. -/
theorem sesquilinearForm_context_EF_ne (ζ : X) (a b : List (Bool × I))
    (i j : I) (hij : i ≠ j) :
    sesquilinearForm D (algebraWord D ζ (a ++ (true, i) :: (false, j) :: b))
        (algebraWord D ζ []) =
      pi ^ (D.parity i * D.parity j).val *
        sesquilinearForm D (algebraWord D ζ (a ++ (false, j) :: (true, i) :: b))
          (algebraWord D ζ []) := by
  rw [algebraWord_context_EF_ne D ζ a b i j hij]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_pow, bar_pi]


/-- Formal Laurent coefficient exchange for Claim 4, specializing only π. -/
theorem sesquilinearForm_context_EF_ne_coeff (σ : ℚ) (hσ : σ ^ 2 = 1)
    (ζ : X) (a b : List (Bool × I)) (i j : I) (hij : i ≠ j) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm D
      (algebraWord D ζ (a ++ (true, i) :: (false, j) :: b))
      (algebraWord D ζ []))).coeff z =
    σ ^ (D.parity i * D.parity j).val *
      (signLaurent σ hσ (sesquilinearForm D
        (algebraWord D ζ (a ++ (false, j) :: (true, i) :: b))
        (algebraWord D ζ []))).coeff z := by
  rw [sesquilinearForm_context_EF_ne D ζ a b i j hij, map_mul, map_pow,
    signLaurent_pi, ← map_pow, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    smul_eq_mul]

end OddMath.CoveringQuantum.UDot.GenericTensor
