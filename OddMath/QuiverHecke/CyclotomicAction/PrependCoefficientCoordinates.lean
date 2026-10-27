/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrependTensorCoordinates
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightCoefficient

/-!
# Shifted cyclotomic prepend coordinates

The balanced extension (9)–(10) of `PrependCoordinates.md` for the prescribed
shifted coefficient. The equivalence is additive, and right coefficient
compatibility is proved separately using the commuting twisted left action.
Polynomial parity, rather than even polynomial support, is required.
No cancellation, grading on the tensor, or full QP identity is asserted.
-/

noncomputable section
open Categorification
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (r : ℕ)
local notation "C" => InductionAlong.Corner (prependAlgebra D Sc i (r+1) :
  Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))
local notation "T" => InductionAlong.Ind (StringDiagrams.SuperBimodule.toSVec (qCoefficient D Sc i β a ha r)) (prependAlgebra D Sc i (r+1) :
  Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))

/-- Coordinates use the existing shifted coefficient at affine height `r+1`. -/
abbrev qPrependTensorEquiv : ((PrependShuffle (r+1) × ℕ) →₀ (StringDiagrams.SuperBimodule.toSVec (qCoefficient D Sc i β a ha r))) ≃+ T :=
  prependTensorEquiv D Sc i (r+1) (StringDiagrams.SuperBimodule.toSVec (qCoefficient D Sc i β a ha r))

/-- The forward map on canonical shifted representatives. -/
theorem qPrependTensorEquiv_single (q : PrependShuffle (r+1) × ℕ)
    (b : CyclotomicAlgebra D Sc a r) :
    qPrependTensorEquiv D Sc i β a ha r
      (Finsupp.single q (qCoefficientInsert D Sc i β a ha r b)) =
      InductionAlong.Ind.tmul (prependPBWCorner D Sc i q.1 q.2 1)
        (qCoefficientInsert D Sc i β a ha r b) :=
  prependTensorForward_single D Sc i (r+1) (StringDiagrams.SuperBimodule.toSVec (qCoefficient D Sc i β a ha r)) q _

/-- The inverse retains the twisted left action on the coefficient. -/
theorem qPrependTensorEquiv_symm_tmul (z : C) (y : (StringDiagrams.SuperBimodule.toSVec (qCoefficient D Sc i β a ha r)))
    (q : PrependShuffle (r+1) × ℕ) :
    (qPrependTensorEquiv D Sc i β a ha r).symm (InductionAlong.Ind.tmul z y) q =
      (prependCoordinateEquiv D Sc i (r+1)).symm z q • y := rfl

/-- On inserted coefficients the inverse explicitly applies the parity involution. -/
theorem qPrependTensorEquiv_symm_insert (z : C) (b : CyclotomicAlgebra D Sc a r)
    (q : PrependShuffle (r+1) × ℕ) :
    (qPrependTensorEquiv D Sc i β a ha r).symm
      (InductionAlong.Ind.tmul z (qCoefficientInsert D Sc i β a ha r b)) q =
      qCoefficientInsert D Sc i β a ha r
        (homMatrixTwist D Sc (r+1) (D.parity i * contentSumParity D β)
          ((prependCoordinateEquiv D Sc i (r+1)).symm z q) • b) := by
  rw [qPrependTensorEquiv_symm_tmul, qCoefficientInsert_smul, homMatrixTwist_twice]

/-- The prescribed right cyclotomic action is coordinatewise. -/
theorem qPrependTensorEquiv_symm_right (c : CyclotomicAlgebra D Sc a r) (t : T)
    (q : PrependShuffle (r+1) × ℕ) :
    (qPrependTensorEquiv D Sc i β a ha r).symm
      (targetRightCoefficient D Sc i β a ha r c t) q =
      (qCoefficient D Sc i β a ha r).ract c
        ((qPrependTensorEquiv D Sc i β a ha r).symm t q) := by
  induction t using InductionAlong.Ind.induction_on with
  | zero => simp
  | add t s ht hs => simp [ht, hs, StringDiagrams.SVec.hom_map_add]
  | tmul z y =>
    rw [targetRightCoefficient_tmul, qPrependTensorEquiv_symm_tmul,
      qPrependTensorEquiv_symm_tmul]
    exact (map_smul (targetCoefficientRight D Sc i β a ha r c) _ y).symm

/-- Right multiplication of an inserted coefficient retains its prescribed formula. -/
theorem qPrependTensorEquiv_single_mul (q : PrependShuffle (r+1) × ℕ)
    (b c : CyclotomicAlgebra D Sc a r) :
    qPrependTensorEquiv D Sc i β a ha r
      (Finsupp.single q (qCoefficientInsert D Sc i β a ha r (b*c))) =
      targetRightCoefficient D Sc i β a ha r c
        (qPrependTensorEquiv D Sc i β a ha r
          (Finsupp.single q (qCoefficientInsert D Sc i β a ha r b))) := by
  rw [qPrependTensorEquiv_single, qPrependTensorEquiv_single,
    targetRightCoefficient_tmul, qCoefficientInsert_mul]

end OddMath.QuiverHecke
