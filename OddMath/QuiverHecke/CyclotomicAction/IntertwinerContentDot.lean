/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetTensor

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
