import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.RingTheory.Idempotents
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChains.IntertwinerGrading
import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Intertwiner right

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
end

end

section

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
end

end

section

/-!
# Graded right-dot square for the moving-strand map

The polynomial-variable portion of KKO I, arXiv:1206.5933v2,
Proposition 8.4: the existing right dots have degree `D.parity i` on
`qSourceSpace` and `qTargetSpace`, and the even map Q intertwines them.
The coefficient involution is retained, including on the shifted target.
These are graded right operators, not assertions of signed left-superlinearity.
No full right-superalgebra action, QP identity, or local inversion is concluded.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Scalar restriction of the existing source right dot. -/
def sourceRightDotLinear (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    qSourceSpace D Sc i a ha n →ₗ[k] qSourceSpace D Sc i a ha n :=
    letI : Module k (InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
      inferInstanceAs (Module k (qSourceSpace D Sc i a ha n))
    letI : IsScalarTower k (Hn D Sc (n + 1 + 1))
      (InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
        (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
      inferInstanceAs (IsScalarTower k (Hn D Sc (n + 1 + 1))
        ((InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
          Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) ⊗[ℤ] CyclotomicAlgebra D Sc a n) ⧸
          BalancedTensor.rel ℤ (Hn D Sc (n + 1 + 1)) (Hn D Sc (n + 1)) _ _))
    (sourceRightDot D Sc i a ha n).restrictScalars k

/-- Scalar restriction of the existing target right dot. -/
def targetRightDotLinear (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    qTargetSpace D Sc i β a ha n →ₗ[k] qTargetSpace D Sc i β a ha n :=
    letI : Module k (InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
      inferInstanceAs (Module k (qTargetSpace D Sc i β a ha n))
    letI : IsScalarTower k (Hn D Sc (n + 1 + 1))
      (InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
        (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
      inferInstanceAs (IsScalarTower k (Hn D Sc (n + 1 + 1))
        ((InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
          Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) ⊗[ℤ] (qCoefficient D Sc i β a ha n).toSVec) ⧸
          BalancedTensor.rel ℤ (Hn D Sc (n + 1 + 1)) (Hn D Sc (n + 1)) _ _))
    (targetRightDot D Sc i β a ha n).restrictScalars k

end OddMath.QuiverHecke
end

end

section

/-!
# Parity-skew polynomials on the induced quotients

The right polynomial action in KKO I, Proposition 8.4. Coefficients are
written first: `c X^m` applies the coefficient and then the dots. Thus the
representation takes values in the ordinary opposite endomorphism ring,
not the super-opposite. The relation is `X c = φ(c) X`, where
`φ(c) = (-1)^(p(i)|c|) c`; no square-zero relation is imposed on `X`.
The coefficient action on the target retains its existing parity shift.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The parity sign is a ring endomorphism of the existing coefficient algebra. -/
def coefficientParityHom (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p : ZMod 2) :
    CyclotomicAlgebra D Sc a n →+* CyclotomicAlgebra D Sc a n where
  toFun := (cyclotomicSuperspace D Sc a ha n).sgn p
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [SVec.sgn_apply_of_mem p (show (1 : CyclotomicAlgebra D Sc a n) ∈
      cyclotomicParity D Sc a ha n 0 from SetLike.GradedOne.one_mem)]
    simp
  map_mul' b c := by
    induction b using SuperBimodule.alg_induction_on (cyclotomicParity D Sc a ha n) with
    | zero => simp
    | add b b' hb hb' => simp only [add_mul, map_add, hb, hb']
    | hom q b hb =>
      induction c using SuperBimodule.alg_induction_on (cyclotomicParity D Sc a ha n) with
      | zero => simp
      | add c c' hc hc' => simp only [mul_add, map_add, hc, hc']
      | hom r c hc =>
        have hbc : b * c ∈ cyclotomicParity D Sc a ha n (q + r) :=
          SetLike.GradedMul.mul_mem hb hc
        rw [SVec.sgn_apply_of_mem p hbc,
          SVec.sgn_apply_of_mem p hb, SVec.sgn_apply_of_mem p hc]
        simp only [add_mul, sign_add, smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [mul_comm (sign k (q * p))]

/-- Powers of the parity twist, as the action required by Mathlib skew polynomials. -/
@[instance_reducible] def coefficientParityAction (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    MulSemiringAction (Multiplicative ℕ) (CyclotomicAlgebra D Sc a n) where
  smul m := coefficientParityHom D Sc a ha n ((m.toAdd : ZMod 2) * D.parity i)
  smul_zero m := map_zero _
  smul_add m := map_add _
  smul_one m := map_one _
  smul_mul m := map_mul _
  one_smul b := by
    change (cyclotomicSuperspace D Sc a ha n).sgn ((0 : ZMod 2) * D.parity i) b = b
    simp
  mul_smul m l b := by
    change (cyclotomicSuperspace D Sc a ha n).sgn
      (((m.toAdd + l.toAdd : ℕ) : ZMod 2) * D.parity i) b =
      ((cyclotomicSuperspace D Sc a ha n).sgn ((m.toAdd : ZMod 2) * D.parity i))
        ((cyclotomicSuperspace D Sc a ha n).sgn ((l.toAdd : ZMod 2) * D.parity i) b)
    rw [← LinearMap.comp_apply, SVec.sgn_comp_sgn, Nat.cast_add, add_mul]

end OddMath.QuiverHecke
end

end
