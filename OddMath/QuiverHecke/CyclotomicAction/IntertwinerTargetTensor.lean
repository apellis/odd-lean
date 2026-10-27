/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentTensor

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

/-- Projection of a shifted coefficient by the even content identity. -/
def qContentCoefficientCut (b : (qCoefficient D Sc i β a ha n).toSVec) :
    qContentCoefficient D Sc i β a ha n :=
  ⟨contentIdempotent D Sc (n + 1) β • b, by
    change _ • (_ • b) = _
    rw [← mul_smul, contentIdempotent_sq]⟩

/-- Include the two factors into the height-indexed tensor. -/
def contentTargetForward : contentTargetTensor D Sc i β a ha n →ₗ[Hn D Sc (n + 1 + 1)]
    InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (ContentTensor.cornerIn _ _ _ x) b.1)
    (fun x y b => by
      have h : ContentTensor.cornerIn _ _ _ (x + y) =
          ContentTensor.cornerIn _ _ _ x + ContentTensor.cornerIn _ _ _ y := rfl
      rw [h]
      exact InductionAlong.Ind.add_tmul _ _ b.1)
    (fun x b c => by
      change InductionAlong.Ind.tmul (ContentTensor.cornerIn _ _ _ x) (b.1 + c.1) = _
      exact InductionAlong.Ind.tmul_add _ b.1 c.1)
    (fun x r b => by
      change InductionAlong.Ind.tmul (op r.1 • ContentTensor.cornerIn _ _ _ x) b.1 =
        InductionAlong.Ind.tmul (ContentTensor.cornerIn _ _ _ x) (r.1 • b.1)
      exact InductionAlong.Ind.op_smul_tmul _ r.1 b.1)
    (fun r x b => by
      change InductionAlong.Ind.tmul (r • ContentTensor.cornerIn _ _ _ x) b.1 =
        r • InductionAlong.Ind.tmul (ContentTensor.cornerIn _ _ _ x) b.1
      exact (InductionAlong.Ind.smul_tmul r _ b.1).symm)

/-- Cut the prepend factor and the shifted coefficient independently. -/
def contentTargetBackward :
    InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
    →ₗ[Hn D Sc (n + 1 + 1)] contentTargetTensor D Sc i β a ha n :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (ContentTensor.cutCorner _ _ _ x)
      (qContentCoefficientCut D Sc i β a ha n b))
    (fun x y b => by
      rw [← InductionAlong.Ind.add_tmul]
      congr 1
      exact Subtype.ext (add_mul _ _ _))
    (fun x b c => by
      rw [← InductionAlong.Ind.tmul_add]
      congr 1
      exact Subtype.ext (smul_add _ _ _))
    (fun x r b => by
      have hx : ContentTensor.cutCorner _ (contentIdempotent D Sc (n + 1) β)
          (contentIdempotent_sq D Sc (n + 1) β) (op r • x) =
          op (ContentTensor.cut (contentIdempotent D Sc (n + 1) β)
            (contentIdempotent_sq D Sc (n + 1) β) (contentIdempotent_central D Sc (n + 1) β) r) •
            ContentTensor.cutCorner _ (contentIdempotent D Sc (n + 1) β)
              (contentIdempotent_sq D Sc (n + 1) β) x := by
        apply Subtype.ext
        change x.1 * prependAlgebra D Sc i (n + 1) r * prependAlgebra D Sc i (n + 1) _ =
          (x.1 * prependAlgebra D Sc i (n + 1) _) * prependAlgebra D Sc i (n + 1) (_ * r)
        rw [mul_assoc, ← map_mul, ← contentIdempotent_central]
        symm
        rw [mul_assoc, ← map_mul, ← mul_assoc, contentIdempotent_sq]
      rw [hx, InductionAlong.Ind.op_smul_tmul]
      congr 1
      apply Subtype.ext
      change (_ * r) • (_ • b) = _ • (r • b)
      rw [← mul_smul, mul_assoc, ← contentIdempotent_central D Sc (n + 1) β r,
        ← mul_assoc, contentIdempotent_sq, mul_smul])
    (fun r x b => by
      rw [InductionAlong.Ind.smul_tmul]
      congr 1
      exact Subtype.ext (mul_assoc _ _ _))

/-- Recutting an included content tensor is identity. -/
theorem contentTargetBackward_forward (z : contentTargetTensor D Sc i β a ha n) :
    contentTargetBackward D Sc i β a ha n (contentTargetForward D Sc i β a ha n z) = z := by
  induction z using InductionAlong.Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul x b =>
    change InductionAlong.Ind.tmul (ContentTensor.cutCorner _ _ _ (ContentTensor.cornerIn _ _ _ x))
      (qContentCoefficientCut D Sc i β a ha n b.1) = InductionAlong.Ind.tmul x b
    have hx : ContentTensor.cutCorner _ _ _ (ContentTensor.cornerIn _ _ _ x) = x := Subtype.ext x.2
    have hb : qContentCoefficientCut D Sc i β a ha n b.1 = b := Subtype.ext b.2
    rw [hx, hb]

/-- On the height tensor the reverse composite is the content projector. -/
theorem contentTargetForward_backward (z) :
    contentTargetForward D Sc i β a ha n (contentTargetBackward D Sc i β a ha n z) =
      targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β) z := by
  induction z using InductionAlong.Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul x b =>
    obtain ⟨b, rfl⟩ := qCoefficientInsert_surjective D Sc i β a ha n b
    change InductionAlong.Ind.tmul (op (contentIdempotent D Sc (n + 1) β) • x)
      (contentIdempotent D Sc (n + 1) β • qCoefficientInsert D Sc i β a ha n b) = _
    rw [targetContent_project_tmul, InductionAlong.Ind.op_smul_tmul,
      InductionAlong.Ind.op_smul_tmul, ← mul_smul, contentIdempotent_sq]

/-- The explicit inclusion and cut comparison with the shifted content summand. -/
def contentTargetEquiv : contentTargetTensor D Sc i β a ha n ≃ₗ[Hn D Sc (n + 1 + 1)]
    qTargetContent D Sc i β a ha n where
  toFun z := ⟨contentTargetForward D Sc i β a ha n z, by
    rw [mem_qTargetContent, ← contentTargetForward_backward, contentTargetBackward_forward]⟩
  invFun z := contentTargetBackward D Sc i β a ha n z.1
  left_inv := contentTargetBackward_forward D Sc i β a ha n
  right_inv z := Subtype.ext ((contentTargetForward_backward D Sc i β a ha n z.1).trans
    ((mem_qTargetContent D Sc i β a ha n z.1).mp z.2))
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' r x := Subtype.ext (map_smul _ r x)

/-- The coefficient cut retains the canonical parity-shift insertion. -/
theorem qContentCoefficientCut_insert (b : CyclotomicAlgebra D Sc a n) :
    (qContentCoefficientCut D Sc i β a ha n (qCoefficientInsert D Sc i β a ha n b)).1 =
      qCoefficientInsert D Sc i β a ha n (b * cyclotomicContentIdempotent D Sc a n β) :=
  (qCoefficientInsert_content D Sc i β a ha n b).symm

/-- Inclusion of a cut representative is the prescribed fixed-content target. -/
theorem contentTargetEquiv_cut_tmul
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    contentTargetEquiv D Sc i β a ha n
      (InductionAlong.Ind.tmul (ContentTensor.cutCorner _ _ _ x)
        (qContentCoefficientCut D Sc i β a ha n (qCoefficientInsert D Sc i β a ha n b))) =
      targetContentTensor D Sc i β a ha n x b := by
  apply Subtype.ext
  exact (contentTargetForward_backward D Sc i β a ha n
    (InductionAlong.Ind.tmul x (qCoefficientInsert D Sc i β a ha n b))).trans
      (targetContent_project_tmul D Sc i β a ha n x b)

/-- Q between the separately defined tensors over the unital content algebra. -/
def contentTensorShiftedQ : contentSourceTensor D Sc i β a n →ₗ[Hn D Sc (n + 1 + 1)]
    contentTargetTensor D Sc i β a ha n :=
  (contentTargetEquiv D Sc i β a ha n).symm.toLinearMap.comp (contentTensorQ D Sc i β a n ha)

/-- The prescribed Q formula uses cuts of the moving strand and the canonical shift. -/
theorem contentTensorShiftedQ_representative
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    contentTensorShiftedQ D Sc i β a ha n (contentSourceRepresentative D Sc i β a n x b) =
      InductionAlong.Ind.tmul
        (ContentTensor.cutCorner _ _ _ (qPrependCorner D Sc i (n + 1) β
          (InductionAlong.cornerMul (contentMove_intertwines D Sc i (n + 1) β) x)))
        (qContentCoefficientCut D Sc i β a ha n (qCoefficientInsert D Sc i β a ha n b)) := by
  change contentTargetBackward D Sc i β a ha n
    (contentTensorQ D Sc i β a n ha (contentSourceRepresentative D Sc i β a n x b)).1 = _
  rw [contentTensorQ_representative]
  rfl

end OddMath.QuiverHecke
