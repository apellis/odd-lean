/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerParity
import OddMath.QuiverHecke.CyclotomicAction.LastDot

/-!
# Right dot on the source of the moving-strand map

KKO I, arXiv:1206.5933v2, Proposition 8.4 uses right multiplication
by the last dot together with the coefficient parity involution. These
are ordinary left-linear operators on the underlying balanced carriers;
no induced tensor grading is asserted here.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification MulOpposite
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The coefficient involution `φ_i` of KKO I. -/
def rightDotCoefficient (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    CyclotomicAlgebra D Sc a n →ₗ[k] CyclotomicAlgebra D Sc a n :=
  (SuperBimodule.regular (cyclotomicParity D Sc a ha n)).toSVec.sgn (D.parity i)

/-- The coefficient involution twists the old algebra action. -/
theorem rightDotCoefficient_smul (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (r : Hn D Sc (n + 1))
    (b : CyclotomicAlgebra D Sc a n) :
    rightDotCoefficient D Sc i a ha n (r • b) =
      homMatrixTwist D Sc (n + 1) (D.parity i) r • rightDotCoefficient D Sc i a ha n b := by
  induction r using SuperBimodule.alg_induction_on (affineParity D Sc (n + 1)) with
  | zero => simp
  | add r s hr hs => simp only [add_smul, map_add, hr, hs]
  | hom p r hr =>
    let V := SuperBimodule.regular (cyclotomicParity D Sc a ha n)
    have h := LinearMap.congr_fun (SVec.sgn_comp_of_mem
      (V.lact_mem p (cyclotomicMk D Sc a n r) (cyclotomicMk_parity D Sc a ha n hr))
      (D.parity i)) b
    rw [homMatrixTwist_of_affineParity D Sc _ _ _ _ hr]
    change _ = (cyclotomicMk D Sc a n (Supercategory.sign k (D.parity i * p) • r)) * _
    rw [map_smul (cyclotomicMk D Sc a n), smul_mul_assoc]
    change V.toSVec.sgn (D.parity i) (V.lact (cyclotomicMk D Sc a n r) b) = _
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, SVec.coe_toLinearMap,
      V, SuperBimodule.regular_lact_apply, rightDotCoefficient, mul_comm p] at h ⊢
    convert h using 1

/-- Supercommutation, written without a homogeneity restriction. -/
theorem affineLastDot_twist_comm (i : I) (n : ℕ) (r : Hn D Sc n) :
    appendAlgebra D Sc i n r * affineLastDot D Sc i n =
      affineLastDot D Sc i n * appendAlgebra D Sc i n (homMatrixTwist D Sc n (D.parity i) r) := by
  induction r using SuperBimodule.alg_induction_on (affineParity D Sc n) with
  | zero => simp
  | add r s hr hs => simp only [map_add, add_mul, mul_add, hr, hs]
  | hom p r hr =>
    rw [homMatrixTwist_of_affineParity D Sc _ _ _ _ hr, map_smul, mul_smul_comm,
      Supercategory.sign_mul, Int.cast_smul_eq_zsmul]
    simpa only [Supercategory.koszulSign_comm (D.parity i) p] using affineLastDot_comm D Sc i n hr

/-- Right multiplication by the last dot preserves the append corner. -/
def rightDotCorner (i : I) (n : ℕ) :
    InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))
      →ₗ[Hn D Sc (n + 1)]
    InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) where
  toFun x := ⟨x.1 * affineLastDot D Sc i n, by
    change (x.1 * affineLastDot D Sc i n) * appendAlgebra D Sc i n 1 = _
    rw [mul_assoc, affineLastDot_mul_append_one]⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' r x := Subtype.ext (mul_assoc _ _ _)

/-- Balance requires the involution; bare right multiplication does not suffice. -/
theorem rightDotCorner_op_smul (i : I) (n : ℕ)
    (x : InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)))
    (r : Hn D Sc n) :
    rightDotCorner D Sc i n (op r • x) =
      op (homMatrixTwist D Sc n (D.parity i) r) • rightDotCorner D Sc i n x := by
  apply Subtype.ext
  change (x.1 * appendAlgebra D Sc i n r) * affineLastDot D Sc i n = _
  rw [mul_assoc, affineLastDot_twist_comm, ← mul_assoc]
  rfl

/-- The source right `t_i` operator on the existing balanced tensor quotient. -/
def sourceRightDot (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    Module.End (Hn D Sc (n + 1 + 1))
      (InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
        (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (rightDotCorner D Sc i (n + 1) x)
      (rightDotCoefficient D Sc i a ha n b))
    (by intros; rw [map_add, InductionAlong.Ind.add_tmul])
    (by intros; rw [map_add, InductionAlong.Ind.tmul_add])
    (by intros; rw [rightDotCorner_op_smul, InductionAlong.Ind.op_smul_tmul,
      rightDotCoefficient_smul])
    (by intros; rw [map_smul, InductionAlong.Ind.smul_tmul])

/-- The involution has the prescribed sign on homogeneous coefficients. -/
theorem rightDotCoefficient_of_mem (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p : ZMod 2)
    (b : CyclotomicAlgebra D Sc a n) (hb : b ∈ cyclotomicParity D Sc a ha n p) :
    rightDotCoefficient D Sc i a ha n b = Supercategory.sign k (p * D.parity i) • b := by
  have h := SVec.sgn_apply_of_mem (D.parity i)
    ((SuperBimodule.mem_regularSVec_part_iff (cyclotomicParity D Sc a ha n)).mpr hb)
  convert h using 1
  rfl

/-- On pure tensors, the source action includes the coefficient involution. -/
@[simp] theorem sourceRightDot_tmul (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    sourceRightDot D Sc i a ha n (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul (rightDotCorner D Sc i (n + 1) x)
        (rightDotCoefficient D Sc i a ha n b) := rfl

end OddMath.QuiverHecke
