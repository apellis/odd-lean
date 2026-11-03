/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendMate
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyRho

/-! # Affine relations in the untruncated old content quotient

The local action of BE (1.13)–(1.14) requires the literal positive old equal crossing to be square-zero
and to satisfy both signed dot slides. All relations descend directly
from affine relations through the full-coefficient old quotient. The
stored content targets are cons lists, while underlying words append
on the right. These are the coefficient inputs for the probe local action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem oldDot_affine (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i]) s.word.length)) := by
  rw [oldAppendDotComponent_eq, appendMovingPower, pow_one]

private theorem oldLowerDot_affine (i : I) (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff i s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i] ++ [i]) s.word.length)) := by
  rw [oldDot_affine]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (s.word ++ [i] ++ [i])).mkQ
    (rightContext D Sc cutoff [i] (s.word ++ [i]) (s.word ++ [i])
      (affineUnit D Sc cutoff (s.word ++ [i]) (s.word ++ [i])
        (dotE D Sc (s.word ++ [i]) s.word.length))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (s.word ++ [i] ++ [i])).mkQ
    (affineUnit D Sc cutoff (s.word ++ [i] ++ [i]) (s.word ++ [i] ++ [i])
      (dotE D Sc (s.word ++ [i]) s.word.length ▷ (pres D Sc).obj (ob D [i]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i]) [i] s.word.length (by simp)]

private theorem oldUpperDot_affine (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff i).obj s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i] ++ [i]) (s.word.length + 1))) := by
  simpa only [append, List.length_append, List.length_singleton] using
    oldDot_affine D Sc cutoff i ((append D Sc cutoff i).obj s)

private theorem affineCrossLast_square (v : List I) (i : I) :
    crossLast D Sc v i i ≫ crossLast D Sc v i i = 0 := by
  have he := crossE_mul_crossE D Sc (w := v ++ [i] ++ [i]) v [] i
    (j := v.length) rfl (by simp [List.append_assoc])
  have hc : crossE D Sc (v ++ [i] ++ [i]) v.length = crossLast D Sc v i i := by
    unfold crossE
    rw [genE_eq D Sc (by simpa using sChain_crossAt v [] i i)]
    rfl
  simpa only [hc, End.mul_def] using he

private theorem oldCross_square (i : I) (s : OldCategory D Sc cutoff) :
    equalCrossComponent D Sc cutoff i s ≫ equalCrossComponent D Sc cutoff i s = 0 := by
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
    ((ideal D Sc cutoff _ _).mkQ _) = 0
  rw [oldComp_mk, ← affineUnit_comp, affineCrossLast_square, map_zero, map_zero]

private theorem affine_slideLeft (v : List I) (i : I) :
    affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) v.length) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc v i i) -
      sign k (D.parity i * D.parity i) •
        (affineUnit D Sc cutoff _ _ (crossLast D Sc v i i) ≫
          affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) (v.length + 1))) = 𝟙 _ := by
  have h := congrArg (affineUnit D Sc cutoff _ _) (dotE_comp_crossLast_self D Sc (i := i) v)
  rw [map_add, map_smul, affineUnit_comp, affineUnit_comp, affineUnit_id,
    ← sign_eq_zsign] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

private theorem affine_slideRight (v : List I) (i : I) :
    affineUnit D Sc cutoff _ _ (crossLast D Sc v i i) ≫
        affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) v.length) -
      sign k (D.parity i * D.parity i) •
        (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) (v.length + 1)) ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc v i i)) = 𝟙 _ := by
  have h := congrArg (affineUnit D Sc cutoff _ _) (crossLast_comp_dotE_self D Sc (i := i) v)
  rw [map_add, map_smul, affineUnit_comp, affineUnit_comp, affineUnit_id,
    ← sign_eq_zsign] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

private theorem oldCross_slideLeft (i : I) (s : OldCategory D Sc cutoff) :
    (show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
      (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff i s)) ≫
        equalCrossComponent D Sc cutoff i s -
      sign k (D.parity i * D.parity i) •
        (equalCrossComponent D Sc cutoff i s ≫
          (show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
            oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff i).obj s))) = 𝟙 _ := by
  rw [oldLowerDot_affine, oldUpperDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) - sign k (D.parity i * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = (ideal D Sc cutoff _ _).mkQ (𝟙 _)
  rw [oldComp_mk, oldComp_mk, ← map_smul, ← map_sub]
  exact congrArg (ideal D Sc cutoff _ _).mkQ (affine_slideLeft D Sc cutoff s.word i)

private theorem oldCross_slideRight (i : I) (s : OldCategory D Sc cutoff) :
    equalCrossComponent D Sc cutoff i s ≫
        (show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
          (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff i s)) -
      sign k (D.parity i * D.parity i) •
        ((show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
          oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff i).obj s)) ≫
          equalCrossComponent D Sc cutoff i s) = 𝟙 _ := by
  rw [oldLowerDot_affine, oldUpperDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) - sign k (D.parity i * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = (ideal D Sc cutoff _ _).mkQ (𝟙 _)
  rw [oldComp_mk, oldComp_mk, ← map_smul, ← map_sub]
  exact congrArg (ideal D Sc cutoff _ _).mkQ (affine_slideRight D Sc cutoff s.word i)

variable (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc cutoff ν i
local notation "K" => oldContentAppend D Sc cutoff (i :: ν) i
variable (s : OldContentCategory D Sc cutoff ν)
local notation "γ" => oldContentEqualCross D Sc cutoff ν i s
/-- The literal positive last equal crossing is square-zero in the old content quotient. -/
theorem oldContentEqualCross_square : γ ≫ γ = 0 := oldCross_square D Sc cutoff i s.obj

/-- The first signed affine slide uses the literal two selected append dots. -/
theorem oldContentEqualCross_slideLeft :
    (show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
      CategoryTheory.Functor.map K (oldContentAppendDot D Sc cutoff ν i s)) ≫ γ -
      koszulSign (D.parity i) (D.parity i) •
        (γ ≫ (show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
          oldContentAppendDot D Sc cutoff (i :: ν) i (CategoryTheory.Functor.obj J s))) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  exact oldCross_slideLeft D Sc cutoff i s.obj

/-- The second signed affine slide retains the same positive crossing and dots. -/
theorem oldContentEqualCross_slideRight :
    γ ≫ (show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
      CategoryTheory.Functor.map K (oldContentAppendDot D Sc cutoff ν i s)) -
      koszulSign (D.parity i) (D.parity i) •
        ((show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
          oldContentAppendDot D Sc cutoff (i :: ν) i (CategoryTheory.Functor.obj J s)) ≫ γ) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  exact oldCross_slideRight D Sc cutoff i s.obj

end OddMath.QuiverHecke.ELVOld
