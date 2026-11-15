import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChains
import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.RingTheory.Idempotents

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
# Right cyclotomic coefficients on the moving-strand quotients

The coefficient portion of KKO I, arXiv:1206.5933v2, Proposition 8.4.
Right multiplication descends on the existing integral balanced quotients.
The target uses the right action of the parity-shifted regular superbimodule;
its canonical insertion is right-linear without an additional sign.
Composition of right operators reverses multiplication. The dot/coefficient
relation is the supertensor relation, not square-zero for an odd variable.
The finite-colour, positive-height and polynomial-parity restrictions remain;
this does not assert the full content-corner statement of Proposition 8.4.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Right multiplication commutes with the affine action on the coefficient quotient. -/
def sourceCoefficientRight (a : I → _root_.Polynomial k) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n) where
  toFun b := b * c
  map_add' b b' := add_mul b b' c
  map_smul' r b := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact congrArg (cyclotomicMk D Sc a n) (mul_assoc r b c)

/-- The shifted coefficient right action still commutes with its twisted left action. -/
def targetCoefficientRight (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1)) (qCoefficient D Sc i β a ha n).toSVec where
  toFun := (qCoefficient D Sc i β a ha n).ract c
  map_add' := SVec.hom_map_add _
  map_smul' r b := congrArg (fun f => f b)
    ((qCoefficient D Sc i β a ha n).lact_ract (cyclotomicMk D Sc a n r) c)

/-- No right-action sign is inserted by the canonical parity shift. -/
theorem qCoefficientInsert_mul (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    qCoefficientInsert D Sc i β a ha n (b * c) =
      (qCoefficient D Sc i β a ha n).ract c (qCoefficientInsert D Sc i β a ha n b) := by
  exact congrArg (fun f => f b)
    ((Envelope.ζPow k (D.parity i * contentSumParity D β)
      (SuperBimodule.regular (cyclotomicParity D Sc a ha n))).inv.2.2 c)

/-- Descended coefficient multiplication on the source quotient. -/
def sourceRightCoefficient (i : I) (a : I → _root_.Polynomial k) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :=
  InductionAlong.Ind.map (φ := (appendAlgebra D Sc i (n + 1) :
    Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) (sourceCoefficientRight D Sc a n c)

/-- Descended shifted right action on the target quotient. -/
def targetRightCoefficient (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :=
  InductionAlong.Ind.map (φ := (prependAlgebra D Sc i (n + 1) :
    Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) (targetCoefficientRight D Sc i β a ha n c)

@[simp] theorem sourceRightCoefficient_tmul (i : I) (a : I → _root_.Polynomial k) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n)
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) (b : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficient D Sc i a n c (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul x (b * c) := rfl

@[simp] theorem targetRightCoefficient_tmul (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n)
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    targetRightCoefficient D Sc i β a ha n c (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul x ((qCoefficient D Sc i β a ha n).ract c b) := rfl

/-- Q is right-linear for every cyclotomic coefficient on the induced quotients. -/
theorem rightCoefficient_Q (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (targetRightCoefficient D Sc i β a ha n c).comp (parityCyclotomicContentQ D Sc i β a ha n) =
      (parityCyclotomicContentQ D Sc i β a ha n).comp (sourceRightCoefficient D Sc i a n c) := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x b => simp only [LinearMap.comp_apply, parityCyclotomicContentQ_tmul,
      sourceRightCoefficient_tmul, targetRightCoefficient_tmul, qCoefficientInsert_mul]

/-- The descended right action satisfies the mul law. -/
theorem sourceRightCoefficient_mul (i : I) (a : I → _root_.Polynomial k)
    (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficient D Sc i a n (b * c) =
      (sourceRightCoefficient D Sc i a n c).comp (sourceRightCoefficient D Sc i a n b) := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.comp_apply,
      sourceRightCoefficient_tmul, mul_assoc]

/-- The descended right action satisfies the mul law. -/
theorem targetRightCoefficient_mul (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    targetRightCoefficient D Sc i β a ha n (b * c) =
      (targetRightCoefficient D Sc i β a ha n c).comp (targetRightCoefficient D Sc i β a ha n b) := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.comp_apply,
      targetRightCoefficient_tmul, SuperBimodule.ract_mul, SVec.comp_apply]

/-- Scalar restriction of the existing source right coefficient action. -/
def sourceRightCoefficientLinear (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
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
    (sourceRightCoefficient D Sc i a n c).restrictScalars k

/-- Scalar restriction of the existing target right coefficient action. -/
def targetRightCoefficientLinear (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
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
    (targetRightCoefficient D Sc i β a ha n c).restrictScalars k

/-- Additive coefficient law for the descended source action. -/
theorem sourceRightCoefficient_zero (i : I) (a : I → _root_.Polynomial k)
    (n : ℕ) :
    sourceRightCoefficient D Sc i a n 0 = 0 := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.zero_apply,
      sourceRightCoefficient_tmul, mul_zero, InductionAlong.Ind.tmul_zero]

/-- Additive coefficient law for the descended source action. -/
theorem sourceRightCoefficient_add (i : I) (a : I → _root_.Polynomial k)
    (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficient D Sc i a n (b + c) =
      sourceRightCoefficient D Sc i a n b + sourceRightCoefficient D Sc i a n c := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.add_apply,
      sourceRightCoefficient_tmul, mul_add, InductionAlong.Ind.tmul_add]

/-- Additive coefficient law for the descended target action. -/
theorem targetRightCoefficient_zero (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    targetRightCoefficient D Sc i β a ha n 0 = 0 := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.zero_apply,
      targetRightCoefficient_tmul, map_zero, SVec.zero_apply, InductionAlong.Ind.tmul_zero]

/-- Additive coefficient law for the descended target action. -/
theorem targetRightCoefficient_add (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    targetRightCoefficient D Sc i β a ha n (b + c) =
      targetRightCoefficient D Sc i β a ha n b + targetRightCoefficient D Sc i β a ha n c := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.add_apply,
      targetRightCoefficient_tmul, map_add, SVec.add_apply, InductionAlong.Ind.tmul_add]

end OddMath.QuiverHecke
end

end

section

/-!
# Finite right polynomial operators for the moving-strand map

For KKO I, arXiv:1206.5933v2, Proposition 8.4, evaluate ordered finite
polynomials `∑ t^m ⊗ c_m` on the existing source and target quotients.
The order is dot first, coefficient second; composition reverses products.
For homogeneous `b` of degree `q`, multiplying the monomials `t^r ⊗ b`
and `t^s ⊗ c` contributes `(-1)^(s p(i) q)`. All natural exponents
are retained, with no square-zero relation on an odd variable.

This module proves finite-sum equivariance and the signed monomial action
law. The coefficient family is a finitely supported function, not yet a
bundled supertensor algebra. Its multiplication and comparison with the
source's `k[t_i]` supertensor cyclotomic algebra remain to be supplied.
Mathlib's `SkewPolynomial` uses the alternative order `c t^m`.
The finite-colour, positive-height and polynomial-parity restrictions remain.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

private theorem dot_pow_coefficient {V : Type*} [AddCommGroup V] [Module k V]
    (T C : Module.End k V) (e : k) (h : T * C = e • (C * T)) (s : ℕ) :
    T ^ s * C = e ^ s • (C * T ^ s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h,
      smul_mul_assoc, smul_smul, ← pow_succ', mul_assoc, ← pow_succ]
    rw [← pow_succ']

/-- Finite coefficients in the order `t^m ⊗ c_m`; no multiplication is declared. -/
abbrev RightPolynomialCoefficients (a : I → _root_.Polynomial k) (n : ℕ) :=
  ℕ →₀ CyclotomicAlgebra D Sc a n

/-- The ordered monomial `t^m ⊗ c` acts by dots followed by the coefficient. -/
def sourceRightMonomial (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (m : ℕ) :
    CyclotomicAlgebra D Sc a n →+ Module.End k (qSourceSpace D Sc i a ha n) where
  toFun c := sourceRightCoefficientLinear D Sc i a ha n c * sourceRightDotLinear D Sc i a ha n ^ m
  map_zero' := by
    have h : sourceRightCoefficientLinear D Sc i a ha n 0 = 0 := by
      ext z
      exact LinearMap.congr_fun (sourceRightCoefficient_zero D Sc i a n) z
    rw [h, zero_mul]
  map_add' b c := by
    have h : sourceRightCoefficientLinear D Sc i a ha n (b + c) =
        sourceRightCoefficientLinear D Sc i a ha n b + sourceRightCoefficientLinear D Sc i a ha n c := by
      ext z
      exact LinearMap.congr_fun (sourceRightCoefficient_add D Sc i a n b c) z
    rw [h, add_mul]

/-- Evaluation of every finite ordered polynomial on the same quotient carrier. -/
def sourceRightPolynomial (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    RightPolynomialCoefficients D Sc a n →+ Module.End k (qSourceSpace D Sc i a ha n) :=
  Finsupp.liftAddHom (sourceRightMonomial D Sc i a ha n)

@[simp] theorem sourceRightPolynomial_single (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (m : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :
    sourceRightPolynomial D Sc i a ha n (Finsupp.single m c) = sourceRightMonomial D Sc i a ha n m c := by
  simp [sourceRightPolynomial]

/-- The ordered monomial `t^m ⊗ c` acts by dots followed by the coefficient. -/
def targetRightMonomial (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (m : ℕ) :
    CyclotomicAlgebra D Sc a n →+ Module.End k (qTargetSpace D Sc i β a ha n) where
  toFun c := targetRightCoefficientLinear D Sc i β a ha n c * targetRightDotLinear D Sc i β a ha n ^ m
  map_zero' := by
    have h : targetRightCoefficientLinear D Sc i β a ha n 0 = 0 := by
      ext z
      exact LinearMap.congr_fun (targetRightCoefficient_zero D Sc i β a ha n) z
    rw [h, zero_mul]
  map_add' b c := by
    have h : targetRightCoefficientLinear D Sc i β a ha n (b + c) =
        targetRightCoefficientLinear D Sc i β a ha n b + targetRightCoefficientLinear D Sc i β a ha n c := by
      ext z
      exact LinearMap.congr_fun (targetRightCoefficient_add D Sc i β a ha n b c) z
    rw [h, add_mul]

/-- Evaluation of every finite ordered polynomial on the same quotient carrier. -/
def targetRightPolynomial (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    RightPolynomialCoefficients D Sc a n →+ Module.End k (qTargetSpace D Sc i β a ha n) :=
  Finsupp.liftAddHom (targetRightMonomial D Sc i β a ha n)

@[simp] theorem targetRightPolynomial_single (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (m : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :
    targetRightPolynomial D Sc i β a ha n (Finsupp.single m c) = targetRightMonomial D Sc i β a ha n m c := by
  simp [targetRightPolynomial]

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

section

/-!
# Fixed-content restriction of the moving-strand map

KKO I, arXiv:1206.5933v2, Proposition 8.4 uses fixed-content source and
shifted target modules. Their realization inside the height-indexed balanced
quotients is the right image of the cyclotomic content idempotent, not the
entire quotient. The two projection formulas move that idempotent to the
append/prepend corner by balancing. The induction principles show that the
cut representatives generate all of these summands.

`contentCornerQ` restricts the existing Q; its representative formula,
left action, right coefficient action and signed right variable are retained.
No action is transported along an arbitrary equivalence. This is the
fixed-content restriction step, not a new tensor-product equivalence over the
unital content corner algebra. Finite colours, polynomial parity and positive
quotient height are still required; the zero-height case and QP remain open.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The content identity is even in the affine algebra. -/
theorem contentIdempotent_parity (n : ℕ) (β : Multiset I) :
    contentIdempotent D Sc n β ∈ affineParity D Sc n 0 := by
  classical
  unfold contentIdempotent FiniteHomMatrix.localUnit
  apply Submodule.sum_mem
  intro w _ p
  simp only [FiniteHomMatrix.idem, FiniteHomMatrix.single]
  by_cases h : (w, w) = p
  · subst p
    simpa using (Supercategory.id_mem (R := k) (wordObj D Sc w))
  · simp [DFinsupp.single_apply, h]

/-- The cyclotomic content identity remains even. -/
theorem cyclotomicContentIdempotent_parity (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (β : Multiset I) :
    cyclotomicContentIdempotent D Sc a n β ∈ cyclotomicParity D Sc a ha n 0 :=
  cyclotomicMk_parity D Sc a ha n (contentIdempotent_parity D Sc (n + 1) β)

/-- The append content identity acts as identity on the moving-strand element. -/
theorem appendContent_mul_contentMove (i : I) (n : ℕ) (β : Multiset I) :
    appendAlgebra D Sc i n (contentIdempotent D Sc n β) * contentMove D Sc i n β =
      contentMove D Sc i n β := by
  classical
  rw [contentMove, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  change appendLinear D Sc i n
    (∑ t ∈ Finset.univ.filter (fun t : Word I n => wordContent t = β),
      FiniteHomMatrix.idem t) * _ = _
  rw [map_sum, Finset.sum_mul, Finset.sum_eq_single w]
  · simp only [FiniteHomMatrix.idem, appendLinear_single]
    have hi : appendHom D Sc i w w (𝟙 _) = 𝟙 _ := by
      convert MonoidalSupercategory.id_whiskerRight (R := k)
        (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) using 1 <;> rfl
    rw [hi]
    let f : wordObj D Sc (prependWord i w) ⟶ wordObj D Sc (appendWord i w) :=
      moveHom D Sc i [] w.1
    change FiniteHomMatrix.single (appendWord i w) (appendWord i w) (𝟙 _) *
      FiniteHomMatrix.single (appendWord i w) (prependWord i w) f =
      FiniteHomMatrix.single (appendWord i w) (prependWord i w) f
    rw [FiniteHomMatrix.single_mul_single, Category.comp_id]
  · intro t _ ht
    simp only [FiniteHomMatrix.idem, appendLinear_single]
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => ht (appendWord_injective i n h)) _ _
  · intro h
    exact (h hw).elim

variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The source content summand is the right image of the coefficient identity. -/
def qSourceContent : Submodule (Hn D Sc (n + 1 + 1))
    (InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
  LinearMap.ker (sourceRightCoefficient D Sc i a n
    (cyclotomicContentIdempotent D Sc a n β) - LinearMap.id)

/-- The target uses the same content cut on the parity-shifted coefficient. -/
def qTargetContent : Submodule (Hn D Sc (n + 1 + 1))
    (InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
  LinearMap.ker (targetRightCoefficient D Sc i β a ha n
    (cyclotomicContentIdempotent D Sc a n β) - LinearMap.id)

@[simp] theorem mem_qSourceContent (z) : z ∈ qSourceContent D Sc i β a n ↔
    sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β) z = z := by
  simp [qSourceContent, LinearMap.mem_ker, sub_eq_zero]

@[simp] theorem mem_qTargetContent (z) : z ∈ qTargetContent D Sc i β a ha n ↔
    targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β) z = z := by
  simp [qTargetContent, LinearMap.mem_ker, sub_eq_zero]

/-- Q restricts to the content summands of its existing source and shifted target. -/
def contentCornerQ : qSourceContent D Sc i β a n →ₗ[Hn D Sc (n + 1 + 1)]
    qTargetContent D Sc i β a ha n :=
  (parityCyclotomicContentQ D Sc i β a ha n).restrict (by
      intro z hz
      rw [mem_qTargetContent]
      have h := LinearMap.congr_fun (rightCoefficient_Q D Sc i β a ha n
        (cyclotomicContentIdempotent D Sc a n β)) z
      simpa only [LinearMap.comp_apply, (mem_qSourceContent D Sc i β a n z).mp hz] using h)

/-- The source projection is literal multiplication on the coefficient, not identity
on the entire height quotient. -/
theorem sourceContent_project (z) :
    sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β) z ∈
      qSourceContent D Sc i β a n := by
  rw [mem_qSourceContent]
  have h := LinearMap.congr_fun (sourceRightCoefficient_mul D Sc i a n
    (cyclotomicContentIdempotent D Sc a n β) (cyclotomicContentIdempotent D Sc a n β)) z
  simpa only [cyclotomicContentIdempotent_sq, LinearMap.comp_apply] using h.symm

/-- The shifted target projection is idempotent as well. -/
theorem targetContent_project (z) :
    targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β) z ∈
      qTargetContent D Sc i β a ha n := by
  rw [mem_qTargetContent]
  have h := LinearMap.congr_fun (targetRightCoefficient_mul D Sc i β a ha n
    (cyclotomicContentIdempotent D Sc a n β) (cyclotomicContentIdempotent D Sc a n β)) z
  simpa only [cyclotomicContentIdempotent_sq, LinearMap.comp_apply] using h.symm

/-- Balancing identifies the source projection with the fixed append corner
`a e(β,i)`, using multiplication, not a chosen equivalence. -/
theorem sourceContent_project_tmul
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β)
        (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul (op (contentIdempotent D Sc (n + 1) β) • x) b := by
  rw [sourceRightCoefficient_tmul, InductionAlong.Ind.op_smul_tmul]
  congr 1
  rw [← cyclotomicContentIdempotent_central]
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rfl

/-- The shift does not change the action of an even content projector. -/
theorem qCoefficientInsert_content (b : CyclotomicAlgebra D Sc a n) :
    qCoefficientInsert D Sc i β a ha n
        (b * cyclotomicContentIdempotent D Sc a n β) =
      contentIdempotent D Sc (n + 1) β • qCoefficientInsert D Sc i β a ha n b := by
  rw [← cyclotomicContentIdempotent_central]
  have h := qCoefficientInsert_smul D Sc i β a ha n
    (contentIdempotent D Sc (n + 1) β) b
  rw [homMatrixTwist_of_affineParity D Sc _ _ _ _
    (contentIdempotent_parity D Sc (n + 1) β), mul_zero,
    Supercategory.sign_zero, one_smul] at h
  convert h using 1
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rfl

/-- The target projection is the fixed prepend corner `a e(i,β)`, while
retaining the canonical shifted coefficient `π_i^{p(β)} b`. -/
theorem targetContent_project_tmul
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β)
        (InductionAlong.Ind.tmul x (qCoefficientInsert D Sc i β a ha n b)) =
      InductionAlong.Ind.tmul (op (contentIdempotent D Sc (n + 1) β) • x)
        (qCoefficientInsert D Sc i β a ha n b) := by
  rw [targetRightCoefficient_tmul, ← qCoefficientInsert_mul,
    qCoefficientInsert_content, InductionAlong.Ind.op_smul_tmul]

/-- A fixed-content source representative, with its first factor cut by `e(β,i)`. -/
def sourceContentTensor
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) : qSourceContent D Sc i β a n :=
  ⟨InductionAlong.Ind.tmul (op (contentIdempotent D Sc (n + 1) β) • x) b, by
    rw [← sourceContent_project_tmul]
    exact sourceContent_project D Sc i β a n _⟩

/-- The restricted Q is `a e(β,i) ⊗ b ↦ a G_β v ⊗ π_i^{p(β)} b`.
Both the multiplication and the coefficient insertion are the previously constructed maps. -/
@[simp] theorem contentCornerQ_tmul
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    (contentCornerQ D Sc i β a ha n (sourceContentTensor D Sc i β a n x b)).1 =
      InductionAlong.Ind.tmul
        (qPrependCorner D Sc i (n + 1) β
          (InductionAlong.cornerMul (contentMove_intertwines D Sc i (n + 1) β) x))
        (qCoefficientInsert D Sc i β a ha n b) := by
  change InductionAlong.Ind.tmul _ _ = _
  congr 1
  apply Subtype.ext
  change (x.1 * appendAlgebra D Sc i (n + 1) (contentIdempotent D Sc (n + 1) β)) *
      contentMove D Sc i (n + 1) β = x.1 * contentMove D Sc i (n + 1) β
  rw [mul_assoc, appendContent_mul_contentMove]

/-- The canonical shift insertion is onto; no choice of carrier equivalence is used. -/
theorem qCoefficientInsert_surjective :
    Function.Surjective (qCoefficientInsert D Sc i β a ha n) := by
  intro b
  let e := Envelope.ζPow k (D.parity i * contentSumParity D β)
    (SuperBimodule.regular (cyclotomicParity D Sc a ha n))
  refine ⟨e.hom.1 b, ?_⟩
  have h := congrArg (fun f => f.1 b) e.hom_inv_id
  exact h

/-- Every fixed source element is generated additively by the cut representatives. -/
@[elab_as_elim] theorem sourceContent_induction
    (P : qSourceContent D Sc i β a n → Prop)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (htmul : ∀ x b, P (sourceContentTensor D Sc i β a n x b))
    (z : qSourceContent D Sc i β a n) : P z := by
  let f : _ →ₗ[Hn D Sc (n + 1 + 1)] qSourceContent D Sc i β a n :=
    (sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β)).codRestrict
      _ (sourceContent_project D Sc i β a n)
  have hf : f z.1 = z := Subtype.ext ((mem_qSourceContent D Sc i β a n z.1).mp z.2)
  rw [← hf]
  induction z.1 using InductionAlong.Ind.induction_on with
  | zero => simpa only [map_zero] using hzero
  | add x y hx hy => simpa only [map_add] using hadd (f x) (f y) hx hy
  | tmul x b =>
    have he : f (InductionAlong.Ind.tmul x b) = sourceContentTensor D Sc i β a n x b :=
      Subtype.ext (sourceContent_project_tmul D Sc i β a n x b)
    rw [he]
    exact htmul x b

/-- A fixed target representative, retaining its coefficient parity shift. -/
def targetContentTensor
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) : qTargetContent D Sc i β a ha n :=
  ⟨InductionAlong.Ind.tmul (op (contentIdempotent D Sc (n + 1) β) • x)
    (qCoefficientInsert D Sc i β a ha n b), by
      rw [← targetContent_project_tmul]
      exact targetContent_project D Sc i β a ha n _⟩

/-- Every fixed shifted target element is generated by prepend-cut representatives. -/
@[elab_as_elim] theorem targetContent_induction
    (P : qTargetContent D Sc i β a ha n → Prop)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (htmul : ∀ x b, P (targetContentTensor D Sc i β a ha n x b))
    (z : qTargetContent D Sc i β a ha n) : P z := by
  let f : _ →ₗ[Hn D Sc (n + 1 + 1)] qTargetContent D Sc i β a ha n :=
    (targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β)).codRestrict
      _ (targetContent_project D Sc i β a ha n)
  have hf : f z.1 = z := Subtype.ext ((mem_qTargetContent D Sc i β a ha n z.1).mp z.2)
  rw [← hf]
  induction z.1 using InductionAlong.Ind.induction_on with
  | zero => simpa only [map_zero] using hzero
  | add x y hx hy => simpa only [map_add] using hadd (f x) (f y) hx hy
  | tmul x b =>
    obtain ⟨b, rfl⟩ := qCoefficientInsert_surjective D Sc i β a ha n b
    have he : f (InductionAlong.Ind.tmul x (qCoefficientInsert D Sc i β a ha n b)) =
        targetContentTensor D Sc i β a ha n x b :=
      Subtype.ext (targetContent_project_tmul D Sc i β a ha n x b)
    rw [he]
    exact htmul x b

end OddMath.QuiverHecke
end

end

section

/-!
# Source tensor over the unital content algebra

KKO I, arXiv:1206.5933v2, §8, Proposition 8.4 uses the source
`R(β + αᵢ)e(β,i) ⊗[R(β)] RΛ(β)`. Here the coefficient algebra is
Mathlib's unital idempotent corner, and its action is the restricted
cyclotomic quotient map. The first factor is the append left ideal; its
support in the enlarged content block is proved.

`contentSourceEquiv` compares this tensor with `qSourceContent` by inclusion
and explicit cuts of both representatives. Both composites are proved.
`contentTensorQ_representative` applies the comparison to the prescribed Q.
Finite colours and positive coefficient height remain required. Polynomial
parity is required for Q, not for the source comparison. The shifted target
tensor comparison, zero-height case and QP are not asserted here.
-/

noncomputable section
open Categorification MulOpposite
namespace OddMath.QuiverHecke.ContentTensor
universe u
variable {A B C : Type u} [Ring A] [Ring B] [Ring C]
variable (φ : A →ₙ+* B) (q : A →+* C) (e : A) (he : IsIdempotentElem e)

/-- Inclusion of the unital idempotent corner, forgetting its unit. -/
def inclusion : he.Corner →ₙ+* A where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The coefficient corner has the image idempotent as its unit. -/
abbrev Coefficient := (he.map q).Corner

/-- The quotient map restricted to both unital corners. -/
def quotient : he.Corner →+* Coefficient q e he where
  toFun x := ⟨q x.1, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨q y, by
      change q e * q y * q e = q x.1
      simpa only [map_mul] using congrArg q hy⟩⟩
  map_one' := Subtype.ext rfl
  map_zero' := Subtype.ext (map_zero q)
  map_add' x y := Subtype.ext (map_add q x.1 y.1)
  map_mul' x y := Subtype.ext (map_mul q x.1 y.1)

instance coefficientModule : Module he.Corner (Coefficient q e he) :=
  Module.compHom _ (quotient q e he)

/-- The inclusion sends the content unit to the appended content idempotent. -/
def append : he.Corner →ₙ+* B := φ.comp (inclusion e he)

/-- The tensor over the unital corner, with its cyclotomic corner coefficient. -/
abbrev Source := InductionAlong.Ind (Coefficient q e he) (append φ e he)

/-- Inclusion of the smaller left ideal into the height left ideal. -/
def cornerIn (x : InductionAlong.Corner (append φ e he)) : InductionAlong.Corner φ :=
  ⟨x.1, by
    change x.1 * φ 1 = x.1
    have hx : x.1 * φ e = x.1 := x.2
    rw [← hx, mul_assoc, ← map_mul, mul_one]⟩

variable (hc : ∀ a, e * a = a * e)

/-- Multiplication by the central content identity, valued in its unital corner. -/
def cut (a : A) : he.Corner := ⟨e * a, a, by
  change e * a * e = e * a
  rw [mul_assoc, ← hc a, ← mul_assoc, he.eq]⟩

@[simp] theorem cut_val (a : A) : (cut e he hc a).1 = e * a := rfl

/-- The coefficient projection is literal multiplication by the quotient identity. -/
def cutCoefficient (c : C) (hqc : ∀ c, q e * c = c * q e) : Coefficient q e he :=
  ⟨q e * c, c, by
    change q e * c * q e = q e * c
    rw [mul_assoc, ← hqc c, ← mul_assoc, (he.map q).eq]⟩

/-- Cut the first factor by the appended content identity. -/
def cutCorner (x : InductionAlong.Corner φ) : InductionAlong.Corner (append φ e he) :=
  ⟨x.1 * φ e, by
    change x.1 * φ e * φ e = x.1 * φ e
    rw [mul_assoc, ← map_mul, he.eq]⟩

section Comparison
variable [Module A C] (hsmul : ∀ (r : A) (b : C), r • b = q r * b)

/-- Forward representative map: include both factors into the height tensor. -/
def forward : Source φ q e he →ₗ[B] InductionAlong.Ind C φ :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (cornerIn φ e he x) b.1)
    (fun x y b => by
      have h : cornerIn φ e he (x + y) = cornerIn φ e he x + cornerIn φ e he y := rfl
      rw [h]
      exact InductionAlong.Ind.add_tmul (cornerIn φ e he x) (cornerIn φ e he y) b.1)
    (fun x b c => by
      change InductionAlong.Ind.tmul (cornerIn φ e he x) (b.1 + c.1) = _
      exact InductionAlong.Ind.tmul_add (cornerIn φ e he x) b.1 c.1)
    (fun x r b => by
      change InductionAlong.Ind.tmul (op r.1 • cornerIn φ e he x) b.1 =
        InductionAlong.Ind.tmul (cornerIn φ e he x) (q r.1 * b.1)
      rw [InductionAlong.Ind.op_smul_tmul, hsmul])
    (fun r x b => by
      change InductionAlong.Ind.tmul (r • cornerIn φ e he x) b.1 =
        r • InductionAlong.Ind.tmul (cornerIn φ e he x) b.1
      exact (InductionAlong.Ind.smul_tmul r (cornerIn φ e he x) b.1).symm)

variable (hqc : ∀ c, q e * c = c * q e)

/-- Backward representative assignment: cut both factors by the content identities. -/
def backward : InductionAlong.Ind C φ →ₗ[B] Source φ q e he :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (cutCorner φ e he x) (cutCoefficient q e he b hqc))
    (fun x y b => by
      rw [← InductionAlong.Ind.add_tmul]
      congr 1
      exact Subtype.ext (add_mul _ _ _))
    (fun x b c => by
      rw [← InductionAlong.Ind.tmul_add]
      congr 1
      exact Subtype.ext (mul_add _ _ _))
    (fun x r b => by
      have hx : cutCorner φ e he (op r • x) =
          op (cut e he hc r) • cutCorner φ e he x := by
        apply Subtype.ext
        change x.1 * φ r * φ e = (x.1 * φ e) * φ (e * r)
        rw [mul_assoc, ← map_mul, ← hc r]
        symm
        rw [mul_assoc, ← map_mul, ← mul_assoc, he.eq]
      rw [hx, InductionAlong.Ind.op_smul_tmul]
      congr 1
      apply Subtype.ext
      change q (e * r) * (q e * b) = q e * (r • b)
      rw [hsmul, ← mul_assoc, ← map_mul]
      have h : e * r * e = e * r := by
        rw [mul_assoc, ← hc r, ← mul_assoc, he.eq]
      rw [h, map_mul, mul_assoc])
    (fun r x b => by
      rw [InductionAlong.Ind.smul_tmul]
      congr 1
      exact Subtype.ext (mul_assoc _ _ _))

/-- Including and recutting a content tensor is the identity. -/
theorem backward_forward (z : Source φ q e he) :
    backward φ q e he hc hsmul hqc (forward φ q e he hsmul z) = z := by
  induction z using InductionAlong.Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul x b =>
    change InductionAlong.Ind.tmul (cutCorner φ e he (cornerIn φ e he x))
      (cutCoefficient q e he b.1 hqc) = InductionAlong.Ind.tmul x b
    have hx : cutCorner φ e he (cornerIn φ e he x) = x := Subtype.ext x.2
    have hb : cutCoefficient q e he b.1 hqc = b :=
      Subtype.ext ((Subsemigroup.mem_corner_iff (he.map q)).mp b.2).1
    rw [hx, hb]

/-- The other composite is the content projection, not the identity on all heights. -/
theorem forward_backward_tmul (x : InductionAlong.Corner φ) (b : C) :
    forward φ q e he hsmul
      (backward φ q e he hc hsmul hqc (InductionAlong.Ind.tmul x b)) =
        InductionAlong.Ind.tmul x (q e * b) := by
  change InductionAlong.Ind.tmul (op e • x) (q e * b) = _
  rw [InductionAlong.Ind.op_smul_tmul, hsmul, ← mul_assoc, ← map_mul, he.eq]

end Comparison
end OddMath.QuiverHecke.ContentTensor

namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k) (n : ℕ)

/-- The unital affine algebra of the fixed content, with unit `e(β)`. -/
abbrev ContentAlgebra := (show IsIdempotentElem (contentIdempotent D Sc (n + 1) β)
  from contentIdempotent_sq D Sc (n + 1) β).Corner

/-- KKO I §8 source tensor over the unital fixed-content algebra. The first
factor is the left ideal cut by the append inclusion of its unit, and the second
is the corresponding corner of the existing cyclotomic quotient. -/
abbrev contentSourceTensor := ContentTensor.Source
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
  (cyclotomicMk D Sc a n).toRingHom (contentIdempotent D Sc (n + 1) β)
  (contentIdempotent_sq D Sc (n + 1) β)

/-- Inclusion of both factors of the fixed-content source tensor. -/
def contentSourceForward : contentSourceTensor D Sc i β a n →ₗ[Hn D Sc (n + 1 + 1)]
    InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) :=
  ContentTensor.forward _ _ _ _ (fun _ _ => rfl)

/-- The inverse representative assignment cuts the append factor and coefficient. -/
def contentSourceBackward :
    InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
    →ₗ[Hn D Sc (n + 1 + 1)] contentSourceTensor D Sc i β a n :=
  ContentTensor.backward _ _ _ _ (contentIdempotent_central D Sc (n + 1) β)
    (fun _ _ => rfl) (cyclotomicContentIdempotent_central D Sc a n β)

/-- The inclusion followed by the cut assignment is identity on the content tensor. -/
theorem contentSourceBackward_forward (z : contentSourceTensor D Sc i β a n) :
    contentSourceBackward D Sc i β a n (contentSourceForward D Sc i β a n z) = z :=
  ContentTensor.backward_forward _ _ _ _ _ _ _ z

/-- On the height tensor the reverse composite is exactly the existing content projector. -/
theorem contentSourceForward_backward (z) :
    contentSourceForward D Sc i β a n (contentSourceBackward D Sc i β a n z) =
      sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β) z := by
  induction z using InductionAlong.Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul x b =>
    change ContentTensor.forward _ _ _ _ _ (ContentTensor.backward _ _ _ _ _ _ _ _) = _
    rw [ContentTensor.forward_backward_tmul, sourceRightCoefficient_tmul]
    exact congrArg (InductionAlong.Ind.tmul x)
      (cyclotomicContentIdempotent_central D Sc a n β b)

/-- The forward multiplication/inclusion map takes values in the fixed-content source. -/
theorem contentSourceForward_mem (z : contentSourceTensor D Sc i β a n) :
    contentSourceForward D Sc i β a n z ∈ qSourceContent D Sc i β a n := by
  rw [mem_qSourceContent, ← contentSourceForward_backward, contentSourceBackward_forward]

/-- Explicit two-sided comparison with the fixed-content summand, not a chosen bijection. -/
def contentSourceEquiv : contentSourceTensor D Sc i β a n ≃ₗ[Hn D Sc (n + 1 + 1)]
    qSourceContent D Sc i β a n where
  toFun z := ⟨contentSourceForward D Sc i β a n z, contentSourceForward_mem D Sc i β a n z⟩
  invFun z := contentSourceBackward D Sc i β a n z.1
  left_inv := contentSourceBackward_forward D Sc i β a n
  right_inv z := Subtype.ext ((contentSourceForward_backward D Sc i β a n z.1).trans
    ((mem_qSourceContent D Sc i β a n z.1).mp z.2))
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' r x := Subtype.ext (map_smul _ r x)

/-- The inverse representative cuts both tensor factors. -/
def contentSourceRepresentative
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) : contentSourceTensor D Sc i β a n :=
  contentSourceBackward D Sc i β a n (InductionAlong.Ind.tmul x b)

@[simp] theorem contentSourceEquiv_representative
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    contentSourceEquiv D Sc i β a n (contentSourceRepresentative D Sc i β a n x b) =
      sourceContentTensor D Sc i β a n x b := by
  apply Subtype.ext
  exact (contentSourceForward_backward D Sc i β a n (InductionAlong.Ind.tmul x b)).trans
    (sourceContent_project_tmul D Sc i β a n x b)

end OddMath.QuiverHecke
end

end

section

/-!
# Shifted target tensor over the content algebra

For KKO I, arXiv:1206.5933v2, Proposition 8.4, `contentTargetEquiv`
compares the tensor over the unital content algebra with the target content
summand. Its coefficient is a submodule of the existing parity-shifted
coefficient, not a ring. Inclusion and cuts give the two maps.
The downstream map `contentTensorShiftedQ` retains the prescribed representatives.
These are underlying left-module comparisons, not graded identifications.
Finite colours, positive height and polynomial parity remain hypotheses.
-/

noncomputable section
open Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The content submodule of the prescribed shifted coefficient. -/
def qContentCoefficient : Submodule (Hn D Sc (n + 1)) (qCoefficient D Sc i β a ha n).toSVec where
  carrier := {b | contentIdempotent D Sc (n + 1) β • b = b}
  zero_mem' := smul_zero _
  add_mem' {b c} hx hy := by
    change _ • (b + c) = b + c
    rw [smul_add, hx, hy]
  smul_mem' r b hb := by
    change contentIdempotent D Sc (n + 1) β • (r • b) = r • b
    rw [← mul_smul, contentIdempotent_central, mul_smul, hb]

/-- Restrict the existing shifted action to the unital content corner. -/
instance qContentCoefficientModule :
    Module (ContentAlgebra D Sc β n) (qContentCoefficient D Sc i β a ha n) where
  smul r b := ⟨r.1 • b.1, (qContentCoefficient D Sc i β a ha n).smul_mem r.1 b.2⟩
  one_smul b := Subtype.ext b.2
  mul_smul r s b := Subtype.ext (mul_smul r.1 s.1 b.1)
  smul_zero r := Subtype.ext (smul_zero r.1)
  smul_add r b c := Subtype.ext (smul_add r.1 b.1 c.1)
  zero_smul b := Subtype.ext (zero_smul _ b.1)
  add_smul r s b := Subtype.ext (add_smul r.1 s.1 b.1)

/-- Prepending restricted to the unital content algebra. -/
abbrev qPrependAlgebra := ContentTensor.append
  (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
  (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β)

/-- The balanced target tensor with its shifted coefficient module. -/
abbrev contentTargetTensor :=
  InductionAlong.Ind (qContentCoefficient D Sc i β a ha n) (qPrependAlgebra D Sc i β n)

end OddMath.QuiverHecke
end

end

section

/-!
# Right dots on the content tensors

For KKO I, arXiv:1206.5933v2, Proposition 8.4, descend the last-dot and
first-dot operators, paired with their coefficient involutions, directly
through the balanced tensors over the unital content algebra. The target
uses the parity of the shifted coefficient, retaining the prescribed sign.
-/

noncomputable section
open Categorification MulOpposite StringDiagrams
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The parity involution fixes the even content identity. -/
theorem homMatrixTwist_contentIdempotent (p : ZMod 2) :
    homMatrixTwist D Sc (n + 1) p (contentIdempotent D Sc (n + 1) β) =
      contentIdempotent D Sc (n + 1) β := by
  rw [homMatrixTwist_of_affineParity D Sc _ _ _ _
    (contentIdempotent_parity D Sc (n + 1) β), mul_zero,
    Supercategory.sign_zero, one_smul]

/-- Last-dot multiplication restricted to the append content corner. -/
def contentSourceDotCorner :
    Module.End (Hn D Sc (n + 1 + 1)) (InductionAlong.Corner (ContentTensor.append
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
      (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β))) where
  toFun x := ⟨x.1 * affineLastDot D Sc i (n + 1), by
    change x.1 * affineLastDot D Sc i (n + 1) *
      appendAlgebra D Sc i (n + 1) (contentIdempotent D Sc (n + 1) β) = _
    have h := affineLastDot_twist_comm D Sc i (n + 1) (contentIdempotent D Sc (n + 1) β)
    rw [homMatrixTwist_contentIdempotent] at h
    rw [mul_assoc, ← h, ← mul_assoc]
    exact congrArg (· * affineLastDot D Sc i (n + 1)) x.2⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' r x := Subtype.ext (mul_assoc _ _ _)

/-- First-dot multiplication restricted to the prepend content corner. -/
def contentTargetDotCorner :
    Module.End (Hn D Sc (n + 1 + 1)) (InductionAlong.Corner (qPrependAlgebra D Sc i β n)) where
  toFun x := ⟨x.1 * affineFirstDot D Sc i (n + 1), by
    change x.1 * affineFirstDot D Sc i (n + 1) *
      prependAlgebra D Sc i (n + 1) (contentIdempotent D Sc (n + 1) β) = _
    have h := affineFirstDot_twist_comm D Sc i (n + 1) (contentIdempotent D Sc (n + 1) β)
    rw [homMatrixTwist_contentIdempotent] at h
    rw [mul_assoc, ← h, ← mul_assoc]
    exact congrArg (· * affineFirstDot D Sc i (n + 1)) x.2⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' r x := Subtype.ext (mul_assoc _ _ _)

/-- The source coefficient involution restricted to its unital content corner. -/
def contentDotCoefficient (b : ContentTensor.Coefficient (cyclotomicMk D Sc a n).toRingHom
    (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β)) :
    ContentTensor.Coefficient (cyclotomicMk D Sc a n).toRingHom
      (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β) :=
  ⟨rightDotCoefficient D Sc i a ha n b.1, by
    apply (Subsemigroup.mem_corner_iff
      ((show IsIdempotentElem (contentIdempotent D Sc (n + 1) β) from
        contentIdempotent_sq D Sc (n + 1) β).map (cyclotomicMk D Sc a n).toRingHom)).mpr
    have hb := ((Subsemigroup.mem_corner_iff
      ((show IsIdempotentElem (contentIdempotent D Sc (n + 1) β) from
        contentIdempotent_sq D Sc (n + 1) β).map (cyclotomicMk D Sc a n).toRingHom)).mp b.2).1
    have h := rightDotCoefficient_smul D Sc i a ha n (contentIdempotent D Sc (n + 1) β) b.1
    rw [homMatrixTwist_contentIdempotent] at h
    change rightDotCoefficient D Sc i a ha n
      (cyclotomicContentIdempotent D Sc a n β * b.1) =
        cyclotomicContentIdempotent D Sc a n β * rightDotCoefficient D Sc i a ha n b.1 at h
    change cyclotomicContentIdempotent D Sc a n β * b.1 = b.1 at hb
    rw [hb] at h
    exact ⟨h.symm, (cyclotomicContentIdempotent_central D Sc a n β _).symm.trans h.symm⟩⟩

/-- The shifted coefficient involution preserves the content submodule. -/
def qContentDotCoefficient (b : qContentCoefficient D Sc i β a ha n) :
    qContentCoefficient D Sc i β a ha n :=
  ⟨(qCoefficient D Sc i β a ha n).toSVec.sgn (D.parity i) b.1, by
    have h := targetDotCoefficient_smul D Sc i β a ha n (contentIdempotent D Sc (n + 1) β) b.1
    rw [homMatrixTwist_contentIdempotent, b.2] at h
    exact h.symm⟩

/-- Restriction of the parity twist to the even content corner. -/
def contentDotTwist (r : ContentAlgebra D Sc β n) : ContentAlgebra D Sc β n :=
  ⟨homMatrixTwist D Sc (n + 1) (D.parity i) r.1, by
    obtain ⟨s, hs⟩ := r.2
    refine ⟨homMatrixTwist D Sc (n + 1) (D.parity i) s, ?_⟩
    have h := congrArg (homMatrixTwist D Sc (n + 1) (D.parity i)) hs
    change (homMatrixTwistAlgebra D Sc (n + 1) (D.parity i))
      (contentIdempotent D Sc (n + 1) β * s * contentIdempotent D Sc (n + 1) β) = _ at h
    rw [map_mul, map_mul] at h
    change homMatrixTwist D Sc (n + 1) (D.parity i) (contentIdempotent D Sc (n + 1) β) *
      homMatrixTwist D Sc (n + 1) (D.parity i) s *
      homMatrixTwist D Sc (n + 1) (D.parity i) (contentIdempotent D Sc (n + 1) β) = _ at h
    simpa only [homMatrixTwist_contentIdempotent] using h⟩

/-- Independent source last-dot descent, paired with the coefficient involution. -/
def contentSourceRightDot : Module.End (Hn D Sc (n + 1 + 1))
    (contentSourceTensor D Sc i β a n) :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (contentSourceDotCorner D Sc i β n x)
      (contentDotCoefficient D Sc i β a ha n b))
    (by
      intro x y b
      rw [map_add, InductionAlong.Ind.add_tmul])
    (by
      intro x b c
      have h : contentDotCoefficient D Sc i β a ha n (b + c) =
          contentDotCoefficient D Sc i β a ha n b + contentDotCoefficient D Sc i β a ha n c :=
        Subtype.ext (map_add _ _ _)
      rw [h, InductionAlong.Ind.tmul_add])
    (by
      intro x r b
      have hx : contentSourceDotCorner D Sc i β n (op r • x) =
          op (contentDotTwist D Sc i β n r) • contentSourceDotCorner D Sc i β n x := by
        apply Subtype.ext
        change (x.1 * appendAlgebra D Sc i (n + 1) r.1) * _ =
          (x.1 * _) * appendAlgebra D Sc i (n + 1) _
        rw [mul_assoc, affineLastDot_twist_comm, ← mul_assoc]
        rfl
      have hb : contentDotCoefficient D Sc i β a ha n (r • b) =
          contentDotTwist D Sc i β n r • contentDotCoefficient D Sc i β a ha n b := by
        apply Subtype.ext
        exact rightDotCoefficient_smul D Sc i a ha n r.1 b.1
      rw [hx, InductionAlong.Ind.op_smul_tmul, hb])
    (by intros; rw [map_smul, InductionAlong.Ind.smul_tmul])

/-- Independent target first-dot descent with the shifted coefficient involution. -/
def contentTargetRightDot : Module.End (Hn D Sc (n + 1 + 1))
    (contentTargetTensor D Sc i β a ha n) :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (contentTargetDotCorner D Sc i β n x)
      (qContentDotCoefficient D Sc i β a ha n b))
    (by
      intro x y b
      rw [map_add, InductionAlong.Ind.add_tmul])
    (by
      intro x b c
      have h : qContentDotCoefficient D Sc i β a ha n (b + c) =
          qContentDotCoefficient D Sc i β a ha n b + qContentDotCoefficient D Sc i β a ha n c :=
        Subtype.ext (map_add _ _ _)
      rw [h, InductionAlong.Ind.tmul_add])
    (by
      intro x r b
      have hx : contentTargetDotCorner D Sc i β n (op r • x) =
          op (contentDotTwist D Sc i β n r) • contentTargetDotCorner D Sc i β n x := by
        apply Subtype.ext
        change (x.1 * prependAlgebra D Sc i (n + 1) r.1) * _ =
          (x.1 * _) * prependAlgebra D Sc i (n + 1) _
        rw [mul_assoc, affineFirstDot_twist_comm, ← mul_assoc]
        rfl
      have hb : qContentDotCoefficient D Sc i β a ha n (r • b) =
          contentDotTwist D Sc i β n r • qContentDotCoefficient D Sc i β a ha n b := by
        apply Subtype.ext
        exact targetDotCoefficient_smul D Sc i β a ha n r.1 b.1
      rw [hx, InductionAlong.Ind.op_smul_tmul, hb])
    (by intros; rw [map_smul, InductionAlong.Ind.smul_tmul])

/-- The source pure tensor uses the last dot and the coefficient involution. -/
@[simp] theorem contentSourceRightDot_tmul
    (x : InductionAlong.Corner (ContentTensor.append
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
      (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β)))
    (b : ContentTensor.Coefficient (cyclotomicMk D Sc a n).toRingHom
      (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β)) :
    contentSourceRightDot D Sc i β a ha n (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul (contentSourceDotCorner D Sc i β n x)
        (contentDotCoefficient D Sc i β a ha n b) := rfl

/-- The target pure tensor uses the shifted involution, not an unshifted substitute. -/
@[simp] theorem contentTargetRightDot_tmul
    (x : InductionAlong.Corner (qPrependAlgebra D Sc i β n))
    (b : qContentCoefficient D Sc i β a ha n) :
    contentTargetRightDot D Sc i β a ha n (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul (contentTargetDotCorner D Sc i β n x)
        (qContentDotCoefficient D Sc i β a ha n b) := rfl

end OddMath.QuiverHecke
end

end
