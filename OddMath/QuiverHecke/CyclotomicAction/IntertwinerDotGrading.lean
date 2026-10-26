/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerGrading
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetDot

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

/-- The first dot has the parity of the prepended colour. -/
theorem affineFirstDot_parity (i : I) (n : ℕ) :
    affineFirstDot D Sc i n ∈ affineParity D Sc (n + 1) (D.parity i) := by
  apply Submodule.sum_mem
  intro w _
  exact FiniteHomMatrix.single_mem_component _ _
    (MonoidalSupercategory.whiskerRight_mem (wordObj D Sc w) (inductionStrandDot_parity D Sc i))

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

/-- The source right dot is homogeneous on the induced quotient grading. -/
theorem sourceRightDot_parity (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    SVec.ofHom (sourceRightDotLinear D Sc i a ha n) ∈
      SVec.parityHom (qSourceSpace D Sc i a ha n) (qSourceSpace D Sc i a ha n) (D.parity i) := by
  let : Module (Hn D Sc (n + 1)) (cyclotomicSuperspace D Sc a ha n) :=
    inferInstanceAs (Module (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n))
  apply InducedParity.ind_map_mem (cyclotomicSuperspace D Sc a ha n)
    (affineParity D Sc (n + 1)) (affineParity D Sc (n + 1 + 1))
    (appendAlgebra D Sc i (n + 1))
    (fun _ _ h => appendAlgebra_parity D Sc i (n + 1) h)
    (cyclotomicCoefficient_smul_mem D Sc a ha n)
  intro p q x b hx hb
  change sourceRightDot D Sc i a ha n (InductionAlong.Ind.tmul x b) ∈ _
  rw [sourceRightDot_tmul]
  have hc : rightDotCoefficient D Sc i a ha n b ∈ cyclotomicParity D Sc a ha n q := by
    rw [rightDotCoefficient_of_mem D Sc i a ha n q b hb]
    exact Submodule.smul_mem _ _ hb
  have h := qSourceSpace_tmul_mem D Sc i a ha n
    (x := rightDotCorner D Sc i (n + 1) x)
    (SetLike.GradedMul.mul_mem hx (affineLastDot_parity D Sc i (n + 1))) hc
  convert h using 1; abel_nf

/-- The shifted target's coefficient sign preserves degree; its first dot supplies the degree. -/
theorem targetRightDot_parity (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    SVec.ofHom (targetRightDotLinear D Sc i β a ha n) ∈
      SVec.parityHom (qTargetSpace D Sc i β a ha n) (qTargetSpace D Sc i β a ha n) (D.parity i) := by
  apply InducedParity.ind_map_mem (qCoefficient D Sc i β a ha n).toSVec
    (affineParity D Sc (n + 1)) (affineParity D Sc (n + 1 + 1))
    (prependAlgebra D Sc i (n + 1))
    (fun _ _ h => prependAlgebra_parity D Sc i (n + 1) h)
    (qCoefficient_smul_mem D Sc i β a ha n)
  intro p q x b hx hb
  change targetRightDot D Sc i β a ha n (InductionAlong.Ind.tmul x b) ∈ _
  rw [targetRightDot_tmul]
  have hc : (qCoefficient D Sc i β a ha n).toSVec.sgn (D.parity i) b ∈
      (qCoefficient D Sc i β a ha n).toSVec.part q := by
    rw [SVec.sgn_apply_of_mem (D.parity i) hb]
    exact Submodule.smul_mem _ _ hb
  have h := qTargetSpace_tmul_mem D Sc i β a ha n
    (x := targetDotCorner D Sc i (n + 1) x)
    (SetLike.GradedMul.mul_mem hx (affineFirstDot_parity D Sc i (n + 1))) hc
  convert h using 1; abel_nf

/-- The Q square commutes on the same graded carriers, with scalar-restricted maps. -/
theorem rightDot_Q_square (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    (targetRightDotLinear D Sc i β a ha n).comp (parityCyclotomicContentQLinear D Sc i β a ha n) =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp (sourceRightDotLinear D Sc i a ha n) := by
  ext z
  exact LinearMap.congr_fun (targetRightDot_Q D Sc i β a ha n) z

/-- The polynomial-variable square of Proposition 8.4: Q is even, both vertical
operators have the colour degree, and the underlying square commutes. -/
theorem rightDot_Q_gradedSquare (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    SVec.ofHom (parityCyclotomicContentQLinear D Sc i β a ha n) ∈
      SVec.parityHom (qSourceSpace D Sc i a ha n) (qTargetSpace D Sc i β a ha n) 0 ∧
    SVec.ofHom (sourceRightDotLinear D Sc i a ha n) ∈
      SVec.parityHom (qSourceSpace D Sc i a ha n) (qSourceSpace D Sc i a ha n) (D.parity i) ∧
    SVec.ofHom (targetRightDotLinear D Sc i β a ha n) ∈
      SVec.parityHom (qTargetSpace D Sc i β a ha n) (qTargetSpace D Sc i β a ha n) (D.parity i) ∧
    (targetRightDotLinear D Sc i β a ha n).comp (parityCyclotomicContentQLinear D Sc i β a ha n) =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp (sourceRightDotLinear D Sc i a ha n) :=
  ⟨parityCyclotomicContentQ_even D Sc i β a ha n, sourceRightDot_parity D Sc i a ha n,
    targetRightDot_parity D Sc i β a ha n, rightDot_Q_square D Sc i β a ha n⟩

end OddMath.QuiverHecke
