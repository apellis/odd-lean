import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetTensor

/-!
# Right coefficients on content tensors

The coefficient part of KKO I, Proposition 8.4, by balanced representative
maps on the independently defined content tensors. Dot compatibility is separate.
-/
noncomputable section
open Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- Right multiplication on the coefficient corner, before tensor descent. -/
def contentCoefficientRight (c : CyclotomicAlgebra D Sc a n) :
    Module.End (ContentAlgebra D Sc β n)
      (ContentTensor.Coefficient (cyclotomicMk D Sc a n).toRingHom
        (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β)) where
  toFun b := ⟨b.1 * c, by
    have he : IsIdempotentElem (contentIdempotent D Sc (n + 1) β) :=
      contentIdempotent_sq D Sc (n + 1) β
    apply (Subsemigroup.mem_corner_iff (he.map (cyclotomicMk D Sc a n).toRingHom)).mpr
    have hb := (Subsemigroup.mem_corner_iff (he.map (cyclotomicMk D Sc a n).toRingHom)).mp b.2
    change cyclotomicContentIdempotent D Sc a n β * b.1 = b.1 ∧
      b.1 * cyclotomicContentIdempotent D Sc a n β = b.1 at hb
    constructor
    · exact (mul_assoc _ _ _).symm.trans (congrArg (· * c) hb.1)
    · change b.1 * c * cyclotomicContentIdempotent D Sc a n β = b.1 * c
      rw [mul_assoc, ← cyclotomicContentIdempotent_central, ← mul_assoc, hb.2]⟩
  map_add' b d := Subtype.ext (add_mul b.1 d.1 c)
  map_smul' r b := Subtype.ext (mul_assoc _ _ _)

/-- Restriction of the shifted coefficient's right action to content support. -/
def qContentCoefficientRight (c : CyclotomicAlgebra D Sc a n) :
    Module.End (ContentAlgebra D Sc β n) (qContentCoefficient D Sc i β a ha n) where
  toFun b := ⟨targetCoefficientRight D Sc i β a ha n c b.1, by
    change _ • targetCoefficientRight D Sc i β a ha n c b.1 = _
    rw [← map_smul, b.2]⟩
  map_add' b d := Subtype.ext (map_add _ b.1 d.1)
  map_smul' r b := Subtype.ext (map_smul (targetCoefficientRight D Sc i β a ha n c) r.1 b.1)

/-- Balanced descent of `x ⊗ b ↦ x ⊗ bc`, not conjugation by a comparison. -/
def contentSourceRightCoefficient (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1 + 1)) (contentSourceTensor D Sc i β a n) :=
  InductionAlong.Ind.map (contentCoefficientRight D Sc β a n c)

/-- Balanced descent of the existing shifted right coefficient action. -/
def contentTargetRightCoefficient (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1 + 1)) (contentTargetTensor D Sc i β a ha n) :=
  InductionAlong.Ind.map (qContentCoefficientRight D Sc i β a ha n c)

/-- Inclusion compares the source actions on all balanced classes. -/
theorem contentSourceEquiv_rightCoefficient (c : CyclotomicAlgebra D Sc a n)
    (z : contentSourceTensor D Sc i β a n) :
    contentSourceEquiv D Sc i β a n (contentSourceRightCoefficient D Sc i β a n c z) =
      sourceContentRightCoefficient D Sc i β a n c (contentSourceEquiv D Sc i β a n z) := by
  apply Subtype.ext
  change contentSourceForward D Sc i β a n (contentSourceRightCoefficient D Sc i β a n c z) =
    sourceRightCoefficient D Sc i a n c (contentSourceForward D Sc i β a n z)
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul x b => rfl

/-- Inclusion compares the shifted target actions on all balanced classes. -/
theorem contentTargetEquiv_rightCoefficient (c : CyclotomicAlgebra D Sc a n)
    (z : contentTargetTensor D Sc i β a ha n) :
    contentTargetEquiv D Sc i β a ha n (contentTargetRightCoefficient D Sc i β a ha n c z) =
      targetContentRightCoefficient D Sc i β a ha n c (contentTargetEquiv D Sc i β a ha n z) := by
  apply Subtype.ext
  change contentTargetForward D Sc i β a ha n (contentTargetRightCoefficient D Sc i β a ha n c z) =
    targetRightCoefficient D Sc i β a ha n c (contentTargetForward D Sc i β a ha n z)
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul x b => rfl

/-- The prescribed moving-strand map intertwines the independent right actions. -/
theorem contentTensorShiftedQ_rightCoefficient (c : CyclotomicAlgebra D Sc a n)
    (z : contentSourceTensor D Sc i β a n) :
    contentTensorShiftedQ D Sc i β a ha n (contentSourceRightCoefficient D Sc i β a n c z) =
      contentTargetRightCoefficient D Sc i β a ha n c (contentTensorShiftedQ D Sc i β a ha n z) := by
  apply (contentTargetEquiv D Sc i β a ha n).injective
  rw [contentTargetEquiv_rightCoefficient]
  simp only [contentTensorShiftedQ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, contentTensorQ]
  rw [contentSourceEquiv_rightCoefficient, contentCornerQ_rightCoefficient]

/-- The independent source operator acts on the second balanced factor. -/
@[simp] theorem contentSourceRightCoefficient_tmul (c : CyclotomicAlgebra D Sc a n)
    (x : InductionAlong.Corner (ContentTensor.append
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
      (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β)))
    (b : ContentTensor.Coefficient (cyclotomicMk D Sc a n).toRingHom
      (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β)) :
    contentSourceRightCoefficient D Sc i β a n c (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul x (contentCoefficientRight D Sc β a n c b) := rfl

/-- The independent target operator retains the existing shifted right action. -/
@[simp] theorem contentTargetRightCoefficient_tmul (c : CyclotomicAlgebra D Sc a n)
    (x : InductionAlong.Corner (qPrependAlgebra D Sc i β n))
    (b : qContentCoefficient D Sc i β a ha n) :
    contentTargetRightCoefficient D Sc i β a ha n c (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul x (qContentCoefficientRight D Sc i β a ha n c b) := rfl

/-- Composition follows the ordinary opposite-endomorphism convention. -/
theorem contentSourceRightCoefficient_mul (b c : CyclotomicAlgebra D Sc a n)
    (z : contentSourceTensor D Sc i β a n) :
    contentSourceRightCoefficient D Sc i β a n (b * c) z =
      contentSourceRightCoefficient D Sc i β a n c
        (contentSourceRightCoefficient D Sc i β a n b z) := by
  apply (contentSourceEquiv D Sc i β a n).injective
  simp only [contentSourceEquiv_rightCoefficient]
  apply Subtype.ext
  exact LinearMap.congr_fun (sourceRightCoefficient_mul D Sc i a n b c) _

/-- The shifted target has the same ordinary opposite composition order. -/
theorem contentTargetRightCoefficient_mul (b c : CyclotomicAlgebra D Sc a n)
    (z : contentTargetTensor D Sc i β a ha n) :
    contentTargetRightCoefficient D Sc i β a ha n (b * c) z =
      contentTargetRightCoefficient D Sc i β a ha n c
        (contentTargetRightCoefficient D Sc i β a ha n b z) := by
  apply (contentTargetEquiv D Sc i β a ha n).injective
  simp only [contentTargetEquiv_rightCoefficient]
  apply Subtype.ext
  exact LinearMap.congr_fun (targetRightCoefficient_mul D Sc i β a ha n b c) _

end OddMath.QuiverHecke
