/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendCrossingTriangular

/-! # Distinct-colour crossing power slides

The mixed PBW inverse in `DeformedActionAssembly.md` §3 uses the signed
substitution of the moving input dot across the last crossing. Distinct
colours have no divided-difference correction. All old arrows retain their
full exterior coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem crossing_dot_slide (i j : I) (hij : i ≠ j) (s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) :
    appendMovingPower D Sc cutoff i (s ++ [j]) 1 ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c =
      SKM.zsign k (D.parity i * D.parity j) •
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
          rightContext D Sc cutoff [j] _ _ (appendMovingPower D Sc cutoff i s 1 ≫ c)) := by
  have hd : rightContext D Sc cutoff [j] (s ++ [i]) (s ++ [i])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)) =
      affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i] ++ [j]) s.length) := by
    apply congrArg (affineUnit D Sc cutoff (s ++ [i] ++ [j]) (s ++ [i] ++ [j]))
    exact dotE_whiskerRight D Sc (s ++ [i]) [j] s.length (by simp)
  have hs := lastDotE_comp_crossLast_ne D Sc (i := i) s hij.symm
  rw [mul_comm (D.parity j) (D.parity i)] at hs
  simp only [appendMovingPower, pow_one, List.length_append, List.length_singleton]
  rw [rightContext_comp, hd,
    ← Category.assoc (affineUnit D Sc cutoff _ _ _), ← affineUnit_comp,
    hs, map_smul, affineUnit_comp]
  simp only [Linear.smul_comp, Category.assoc]

theorem crossing_power_slide (i j : I) (hij : i ≠ j) (s t : List I) (m : ℕ)
    (c : hom D Sc cutoff (s ++ [i]) t) :
    appendMovingPower D Sc cutoff i (s ++ [j]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c =
      SKM.zsign k (D.parity i * D.parity j) ^ m •
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
          rightContext D Sc cutoff [j] _ _ (appendMovingPower D Sc cutoff i s m ≫ c)) := by
  induction m generalizing c with
  | zero => simp [appendMovingPower, affineUnit_id, End.one_def]
  | succ m ih =>
    have hp (v : List I) : appendMovingPower D Sc cutoff i v (m + 1) =
        appendMovingPower D Sc cutoff i v m ≫ appendMovingPower D Sc cutoff i v 1 := by
      unfold appendMovingPower
      rw [pow_one, pow_succ', End.mul_def, affineUnit_comp]
    rw [hp, Category.assoc, crossing_dot_slide D Sc cutoff i j hij,
      Linear.comp_smul, ih, smul_smul, ← pow_succ']
    rw [hp]
    simp only [Category.assoc]

theorem projection_crossing_power_slide (i j : I) (hij : i ≠ j) (v s t : List I)
    (m : ℕ) (r : hom D Sc cutoff v (s ++ [j])) (c : hom D Sc cutoff (s ++ [i]) t) :
    appendProjection D Sc cutoff i v (t ++ [j])
      (rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [j]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c) =
      SKM.zsign k (D.parity i * D.parity j) ^ m •
        appendProjection D Sc cutoff i v (t ++ [j])
          (rightContext D Sc cutoff [i] _ _ r ≫
            affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
            rightContext D Sc cutoff [j] _ _ (appendMovingPower D Sc cutoff i s m ≫ c)) := by
  rw [crossing_power_slide D Sc cutoff i j hij, Linear.comp_smul, map_smul]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
