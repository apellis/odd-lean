import OddMath.QuiverHecke.CyclotomicAction.PrependDotCancellation
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentDot

/-! Cancellation for the moving dot minus the old last-dot coefficient.

The odd square is a sum of squares; the even complementary product is a
difference of squares. The content tensor embeds only into the fixed-projector
submodule of the full target. This is cancellation, not a global QP identity.
-/

noncomputable section
open StringDiagrams Categorification Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (r : ℕ)
local notation "T" => InductionAlong.Ind
  (StringDiagrams.SuperBimodule.toSVec (qCoefficient D Sc i β a ha r))
  (prependAlgebra D Sc i (r + 1) : Hn D Sc (r + 1) →ₙ+* Hn D Sc (r + 1 + 1))
local notation "d" => targetRightDot D Sc i β a ha r
local notation "R" => targetRightCoefficient D Sc i β a ha r
local notation "z" => cyclotomicMk D Sc a r (affineLastDot D Sc i r)

/-- Negation in the coefficient gives negation of its right action. -/
theorem targetRightCoefficient_neg_apply (c : CyclotomicAlgebra D Sc a r) (t : T) :
    R (-c) t = -(R c t) := by
  have h := LinearMap.congr_fun (targetRightCoefficient_add D Sc i β a ha r c (-c)) t
  have hz := LinearMap.congr_fun (targetRightCoefficient_zero D Sc i β a ha r) t
  simp only [add_neg_cancel, LinearMap.add_apply] at h
  rw [hz] at h
  change (0 : T) = R c t + R (-c) t at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The even moving dot commutes with the old last-dot action. -/
theorem targetRightDot_lastDot_even (hp : D.parity i = 0) (t : T) :
    d (R z t) = R z (d t) := by
  have hc := targetDotCoefficient_ract D Sc i β a ha r (D.parity i) z
    (cyclotomicMk_parity D Sc a ha r (affineLastDot_parity D Sc i r))
  simp only [hp, zero_mul, sign_zero, one_smul] at hc
  induction t using InductionAlong.Ind.induction_on with
  | zero => simp
  | add t s ht hs => simpa only [map_add] using congrArg₂ (· + ·) ht hs
  | tmul x b => simp only [targetRightCoefficient_tmul, targetRightDot_tmul, hp, hc]

/-- The odd moving dot anticommutes with the old last-dot action. -/
theorem targetRightDot_lastDot_odd (hp : D.parity i = 1) (t : T) :
    d (R z t) = -(R z (d t)) := by
  have hc := targetDotCoefficient_ract D Sc i β a ha r (D.parity i) z
    (cyclotomicMk_parity D Sc a ha r (affineLastDot_parity D Sc i r))
  simp only [hp, one_mul, sign_one, neg_one_smul] at hc
  induction t using InductionAlong.Ind.induction_on with
  | zero => simp
  | add t s ht hs => simpa only [map_add, neg_add] using congrArg₂ (· + ·) ht hs
  | tmul x b =>
    simp only [targetRightCoefficient_tmul, targetRightDot_tmul, hp, hc]
    exact BalancedTensor.tmul_neg _ _

/-- The square of the odd difference is the sum of the two squares. -/
theorem targetRightDot_sub_lastDot_odd_square (hp : D.parity i = 1) (t : T) :
    d (d t - R z t) - R z (d t - R z t) = (d ^ 2) t + R (z ^ 2) t := by
  have hm := LinearMap.congr_fun (targetRightCoefficient_mul D Sc i β a ha r z z) t
  change R (z * z) t = R z (R z t) at hm
  rw [map_sub, map_sub, targetRightDot_lastDot_odd D Sc i β a ha r hp,
    pow_two z, hm]
  change d (d t) - -(R z (d t)) - (R z (d t) - R z (R z t)) = d (d t) + R z (R z t)
  abel

/-- The even complementary product is the difference of the two squares. -/
theorem targetRightDot_sub_lastDot_even_product (hp : D.parity i = 0) (t : T) :
    d (d t - R z t) + R z (d t - R z t) = (d ^ 2) t - R (z ^ 2) t := by
  have hm := LinearMap.congr_fun (targetRightCoefficient_mul D Sc i β a ha r z z) t
  change R (z * z) t = R z (R z t) at hm
  rw [map_sub, map_sub, targetRightDot_lastDot_even D Sc i β a ha r hp,
    pow_two z, hm]
  change d (d t) - R z (d t) + (R z (d t) - R z (R z t)) = d (d t) - R z (R z t)
  abel

/-- Cancellation of the signed linear difference, without a nontriviality assumption. -/
theorem targetRightDot_sub_lastDot_injective :
    Function.Injective (fun t : T => d t - R z t) := by
  intro t s h
  rcases parity_eq_zero_or_one (D.parity i) with hp | hp
  · apply targetRightDot_sq_sub_coefficient_injective D Sc i β a ha r (z ^ 2)
    simpa only [targetRightDot_sub_lastDot_even_product D Sc i β a ha r hp] using
      congrArg (fun w => d w + R z w) h
  · apply targetRightDot_sq_sub_coefficient_injective D Sc i β a ha r (-(z ^ 2))
    simpa only [targetRightDot_sub_lastDot_odd_square D Sc i β a ha r hp,
      targetRightCoefficient_neg_apply, sub_neg_eq_add] using
      congrArg (fun w => d w - R z w) h

/-- Cancellation on the content target through its fixed-projector embedding. -/
theorem contentTargetRightDot_sub_lastDot_injective :
    Function.Injective (fun t : contentTargetTensor D Sc i β a ha r =>
      contentTargetRightDot D Sc i β a ha r t -
        contentTargetRightCoefficient D Sc i β a ha r z t) := by
  intro t s h
  apply (contentTargetEquiv D Sc i β a ha r).injective
  apply Subtype.ext
  apply targetRightDot_sub_lastDot_injective D Sc i β a ha r
  have he := congrArg (fun w => (contentTargetEquiv D Sc i β a ha r w).val) h
  simpa only [map_sub, contentTargetEquiv_rightDot, contentTargetEquiv_rightCoefficient,
    Submodule.coe_sub, targetContentRightDot, targetContentRightCoefficient,
    LinearMap.restrict_apply] using he

end OddMath.QuiverHecke
