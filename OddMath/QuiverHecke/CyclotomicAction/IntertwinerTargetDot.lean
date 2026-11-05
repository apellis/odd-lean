/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightDot

/-!
# First-dot action on the parity-shifted moving-strand target

The target right action in KKO I, arXiv:1206.5933v2, Proposition 8.4
uses the parity operator of the shifted coefficient module. No induced
tensor grading is asserted.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The dot on the prepended strand. -/
def inductionFirstDot (i : I) {n : ℕ} (w : Word I n) :
    End (wordObj D Sc (prependWord i w)) :=
  inductionStrandDot D Sc i ▷ wordObj D Sc w

/-- The diagonal first dot in the prepend corner. -/
def affineFirstDot (i : I) (n : ℕ) : Hn D Sc (n + 1) :=
  ∑ w : Word I n, FiniteHomMatrix.single (prependWord i w) (prependWord i w)
    (inductionFirstDot D Sc i w)

private theorem firstDot_mul_entry (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependWord i t)) :
    affineFirstDot D Sc i n * FiniteHomMatrix.single (prependWord i t) (prependWord i s) f =
      FiniteHomMatrix.single (prependWord i t) (prependWord i s)
        (f ≫ inductionFirstDot D Sc i t) := by
  rw [affineFirstDot, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (prependWord_injective i n h)) _ _
  · simp

private theorem entry_mul_firstDot (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependWord i t)) :
    FiniteHomMatrix.single (prependWord i t) (prependWord i s) f * affineFirstDot D Sc i n =
      FiniteHomMatrix.single (prependWord i t) (prependWord i s)
        (inductionFirstDot D Sc i s ≫ f) := by
  rw [affineFirstDot, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (prependWord_injective i n h.symm)) _ _
  · simp

/-- Superinterchange supplies the twist required for balance. -/
theorem affineFirstDot_twist_comm (i : I) (n : ℕ) (r : Hn D Sc n) :
    prependAlgebra D Sc i n r * affineFirstDot D Sc i n =
      affineFirstDot D Sc i n * prependAlgebra D Sc i n (homMatrixTwist D Sc n (D.parity i) r) := by
  induction r using SuperBimodule.alg_induction_on (affineParity D Sc n) with
  | zero => simp
  | add r s hr hs => simp only [map_add, add_mul, mul_add, hr, hs]
  | hom p r hr =>
    rw [homMatrixTwist_of_affineParity D Sc _ _ _ _ hr, map_smul, mul_smul_comm]
    change prependLinear D Sc i n r * _ = _ • (_ * prependLinear D Sc i n r)
    conv_lhs => rw [FiniteHomMatrix.eq_sum_single r, map_sum, Finset.sum_mul]
    conv_rhs => rw [FiniteHomMatrix.eq_sum_single r, map_sum, Finset.mul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [prependLinear_single, entry_mul_firstDot, firstDot_mul_entry]
    have h := MonoidalSupercategory.super_interchange
      (inductionStrandDot_parity D Sc i) (hr q)
    change FiniteHomMatrix.single _ _ (_ ≫ _) = _
    rw [show inductionFirstDot D Sc i q.2 ≫ prependHom D Sc i q.2 q.1 (r q) =
      Supercategory.koszulSign (D.parity i) p •
        (prependHom D Sc i q.2 q.1 (r q) ≫ inductionFirstDot D Sc i q.1) from h]
    rw [Supercategory.sign_mul, Int.cast_smul_eq_zsmul]
    simp only [FiniteHomMatrix.single, DFinsupp.single_smul]

/-- The first dot belongs to the prepend corner. -/
theorem affineFirstDot_mul_prepend_one (i : I) (n : ℕ) :
    affineFirstDot D Sc i n * prependAlgebra D Sc i n 1 = affineFirstDot D Sc i n := by
  change _ * prependLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ) = _
  rw [FiniteHomMatrix.localUnit, map_sum, Finset.mul_sum]
  conv_rhs => unfold affineFirstDot
  apply Finset.sum_congr rfl
  intro w _
  change affineFirstDot D Sc i n * prependLinear D Sc i n
    (FiniteHomMatrix.single w w (𝟙 _)) = _
  rw [prependLinear_single, firstDot_mul_entry]
  rw [show prependHom D Sc i w w (𝟙 _) = 𝟙 _ by
    convert MonoidalSupercategory.whiskerLeft_id (R := k)
      ((pres D Sc).obj (ob D [i])) (wordObj D Sc w) using 1 <;> rfl]
  exact congrArg (FiniteHomMatrix.single _ _) (Category.id_comp _)

/-- Right multiplication by the first dot on the prepend corner. -/
def targetDotCorner (i : I) (n : ℕ) :
    InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))
      →ₗ[Hn D Sc (n + 1)]
    InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) where
  toFun x := ⟨x.1 * affineFirstDot D Sc i n, by
    change (x.1 * affineFirstDot D Sc i n) * prependAlgebra D Sc i n 1 = _
    rw [mul_assoc, affineFirstDot_mul_prepend_one]⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' r x := Subtype.ext (mul_assoc _ _ _)

theorem targetDotCorner_op_smul (i : I) (n : ℕ)
    (x : InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)))
    (r : Hn D Sc n) :
    targetDotCorner D Sc i n (op r • x) =
      op (homMatrixTwist D Sc n (D.parity i) r) • targetDotCorner D Sc i n x := by
  apply Subtype.ext
  change (x.1 * prependAlgebra D Sc i n r) * affineFirstDot D Sc i n = _
  rw [mul_assoc, affineFirstDot_twist_comm, ← mul_assoc]
  rfl

/-- Parity on the shifted coefficient twists its left action. -/
theorem targetDotCoefficient_smul (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (r : Hn D Sc (n + 1))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    (qCoefficient D Sc i β a ha n).toSVec.sgn (D.parity i) (r • b) =
      homMatrixTwist D Sc (n + 1) (D.parity i) r •
        (qCoefficient D Sc i β a ha n).toSVec.sgn (D.parity i) b := by
  induction r using SuperBimodule.alg_induction_on (affineParity D Sc (n + 1)) with
  | zero => simp
  | add r s hr hs => simp only [add_smul, map_add, hr, hs]
  | hom p r hr =>
    let V := qCoefficient D Sc i β a ha n
    have h := LinearMap.congr_fun (SVec.sgn_comp_of_mem
      (V.lact_mem p (cyclotomicMk D Sc a n r) (cyclotomicMk_parity D Sc a ha n hr))
      (D.parity i)) b
    rw [homMatrixTwist_of_affineParity D Sc _ _ _ _ hr]
    change _ = V.lact (cyclotomicMk D Sc a n (Supercategory.sign k (D.parity i * p) • r)) _
    rw [map_smul (cyclotomicMk D Sc a n), map_smul V.lact]
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, SVec.coe_toLinearMap,
      SVec.smul_apply, mul_comm p] at h ⊢
    convert h using 1

/-- The target right dot uses the parity of the shifted coefficient. -/
def targetRightDot (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    Module.End (Hn D Sc (n + 1 + 1))
      (InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
        (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (targetDotCorner D Sc i (n + 1) x)
      ((qCoefficient D Sc i β a ha n).toSVec.sgn (D.parity i) b))
    (by intros; rw [map_add, InductionAlong.Ind.add_tmul])
    (by intros; rw [map_add, InductionAlong.Ind.tmul_add])
    (by intros; rw [targetDotCorner_op_smul, InductionAlong.Ind.op_smul_tmul,
      targetDotCoefficient_smul])
    (by intros; rw [map_smul, InductionAlong.Ind.smul_tmul])

/-- The pure-tensor target formula. -/
@[simp] theorem targetRightDot_tmul (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    targetRightDot D Sc i β a ha n (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul (targetDotCorner D Sc i (n + 1) x)
        ((qCoefficient D Sc i β a ha n).toSVec.sgn (D.parity i) b) := rfl

end OddMath.QuiverHecke
