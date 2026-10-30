/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPCentral
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyRho

/-!
# Full-coefficient append crossing triangularity

The local crossing/output-polynomial separation needed for
`DeformedMackeyBoundary.md` (4)–(5). Every input moving-dot power across
an equal-colour final crossing is a signed old-output-dot crossing plus an
explicit identity output-row polynomial. Arbitrary old input and output
arrows carry the full ELV coefficient algebra; the correction retains the
total-Hom parity twist. The equality projects to the actual append-old
quotient. Global PBW-tail identification, directness, and C0 are not asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The one-dot triangular slide with arbitrary full-coefficient old arrows.
The correction is exactly the identity append row, not an input-tail projection. -/
theorem appendCrossing_dot_triangular (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    rightContext D Sc cutoff [i] _ _ r ≫
        affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g =
      SKM.zsign k (D.parity i * D.parity i) •
        (rightContext D Sc cutoff [i] _ _ r ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _
            (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫ g)) -
      SKM.zsign k (D.parity i * D.parity i) •
        rightContext D Sc cutoff [i] _ _ (r ≫ g) := by
  have hd : rightContext D Sc cutoff [i] (s ++ [i]) (s ++ [i])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)) =
      affineUnit D Sc cutoff (s ++ [i] ++ [i]) (s ++ [i] ++ [i])
        (dotE D Sc (s ++ [i] ++ [i]) s.length) := by
    apply congrArg (affineUnit D Sc cutoff (s ++ [i] ++ [i]) (s ++ [i] ++ [i]))
    exact dotE_whiskerRight D Sc (s ++ [i]) [i] s.length (by simp)
  rw [rightContext_comp, hd,
    ← Category.assoc (affineUnit D Sc cutoff _ _ _), ← affineUnit_comp,
    lastDotE_comp_crossLast_self, map_sub, map_smul, map_smul, affineUnit_comp, affineUnit_id]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
    Linear.comp_smul, Category.assoc, Category.id_comp, rightContext_comp]

/-- Output-polynomial reconstruction on raw full-coefficient Homs. -/
def appendOutputPolynomial (i : I) (v t : List I) :
    (ℕ →₀ hom D Sc cutoff v t) →ₗ[k] hom D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  Finsupp.lsum k fun d =>
    (Linear.rightComp k _ (appendMovingPower D Sc cutoff i t d)).comp
      (rightContext D Sc cutoff [i] v t)

@[simp] theorem appendOutputPolynomial_single (i : I) (v t : List I)
    (d : ℕ) (g : hom D Sc cutoff v t) :
    appendOutputPolynomial D Sc cutoff i v t (Finsupp.single d g) =
      rightContext D Sc cutoff [i] v t g ≫ appendMovingPower D Sc cutoff i t d := by
  simp only [appendOutputPolynomial, Finsupp.lsum_single, LinearMap.comp_apply,
    Linear.rightComp_apply]

/-- Moving powers retain the total parity of the old Hom, including exterior coefficients. -/
theorem appendMovingPower_twisted_rightContext (i : I) (v t : List I) (d : ℕ)
    (g : hom D Sc cutoff v t) :
    appendMovingPower D Sc cutoff i v d ≫ rightContext D Sc cutoff [i] v t g =
      rightContext D Sc cutoff [i] v t (twist k (d • D.parity i) g) ≫
        appendMovingPower D Sc cutoff i t d := by
  rw [appendMovingPower_whisker, appendMovingPower_whisker]
  exact trailing_comp_rightContext D Sc cutoff (firstDot_pow_parity D Sc i [] d) g

/-- Coefficients of the identity-row correction, recursively computed rather than assumed. -/
def appendCrossingCorrection (i : I) (s t : List I) :
    ℕ → hom D Sc cutoff (s ++ [i]) t → (ℕ →₀ hom D Sc cutoff (s ++ [i]) t)
  | 0, _ => 0
  | m + 1, g =>
      SKM.zsign k (D.parity i * D.parity i) •
        appendCrossingCorrection i s t m
          (appendMovingPower D Sc cutoff i s 1 ≫ g) -
      Finsupp.single m (SKM.zsign k (D.parity i * D.parity i) •
        twist k (m • D.parity i) g)

/-- All moving-dot powers across the final equal-colour crossing have an
explicit identity append-row correction over the full ELV coefficient algebra. -/
theorem appendCrossing_power_triangular (i : I) (s t : List I) (m : ℕ)
    (g : hom D Sc cutoff (s ++ [i]) t) :
    appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      appendOutputPolynomial D Sc cutoff i (s ++ [i]) t
        (appendCrossingCorrection D Sc cutoff i s t m g) := by
  induction m generalizing g with
  | zero =>
    simp [appendCrossingCorrection, appendMovingPower, affineUnit_id, End.one_def]
  | succ m ih =>
    have hp (v : List I) : appendMovingPower D Sc cutoff i v (m + 1) =
        appendMovingPower D Sc cutoff i v m ≫ appendMovingPower D Sc cutoff i v 1 := by
      unfold appendMovingPower
      rw [pow_one, pow_succ', End.mul_def, affineUnit_comp]
    have slide : appendMovingPower D Sc cutoff i (s ++ [i]) 1 ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g =
        SKM.zsign k (D.parity i * D.parity i) •
          (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
            rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s 1 ≫ g)) -
        SKM.zsign k (D.parity i * D.parity i) • rightContext D Sc cutoff [i] _ _ g := by
      simpa only [appendMovingPower, pow_one, List.length_append, List.length_singleton,
        appendRightContext_id, Category.id_comp] using
        appendCrossing_dot_triangular D Sc cutoff i (s ++ [i]) s t (𝟙 _) g
    rw [hp, Category.assoc, slide]
    simp only [Preadditive.comp_sub, Linear.comp_smul]
    rw [ih, appendMovingPower_twisted_rightContext]
    rw [appendCrossingCorrection, map_sub, map_smul, appendOutputPolynomial_single,
      map_smul, Linear.smul_comp, smul_add, smul_smul, hp]
    simp only [Category.assoc]
    rw [pow_succ']
    abel

/-- The same triangular identity with an arbitrary full-coefficient old input arrow. -/
theorem appendCrossing_power_triangular_comp (i : I) (v s t : List I) (m : ℕ)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        (rightContext D Sc cutoff [i] _ _ r ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      rightContext D Sc cutoff [i] _ _ r ≫
        appendOutputPolynomial D Sc cutoff i (s ++ [i]) t
          (appendCrossingCorrection D Sc cutoff i s t m g) := by
  rw [appendCrossing_power_triangular, Preadditive.comp_add, Linear.comp_smul]

/-- Projection to the actual append-old quotient preserves the explicit correction.
No quotient by the crossing span, or splitting of that span, is assumed. -/
theorem appendProjection_crossing_power_triangular (i : I) (v s t : List I) (m : ℕ)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendProjection D Sc cutoff i v (t ++ [i])
      (rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g) =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        appendProjection D Sc cutoff i v (t ++ [i])
          (rightContext D Sc cutoff [i] _ _ r ≫
            affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
            rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ r ≫
          appendOutputPolynomial D Sc cutoff i (s ++ [i]) t
            (appendCrossingCorrection D Sc cutoff i s t m g)) := by
  rw [appendCrossing_power_triangular_comp, map_add, map_smul]

/-- Every correction coefficient remains in the identity output row after an old prefix. -/
theorem appendOutputPolynomial_precomp (i : I) (v s t : List I)
    (r : hom D Sc cutoff v s) (f : ℕ →₀ hom D Sc cutoff s t) :
    rightContext D Sc cutoff [i] _ _ r ≫ appendOutputPolynomial D Sc cutoff i s t f =
      appendOutputPolynomial D Sc cutoff i v t
        (Finsupp.lsum k (fun d => (Finsupp.lsingle d).comp (Linear.leftComp k _ r)) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, hf, hg]
  | single d g =>
    simp only [Finsupp.lsum_single, LinearMap.comp_apply, Linear.leftComp_apply,
      Finsupp.lsingle_apply, appendOutputPolynomial_single, rightContext_comp, Category.assoc]

end OddMath.QuiverHecke.ELVOld
