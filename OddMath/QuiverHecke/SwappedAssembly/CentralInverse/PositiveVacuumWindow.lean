/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.TwoSector

/-! # The positive-height inverse window at the two absent vacuum corners

The positive-height counterpart of `negMap_isCupInverse_of_zero_corners`, toward
Brundan–Ellis, *Super Kac–Moody 2-categories*, §8 (research issue #345). When the
reservoir source and probe target of the two-sector map with `H` cap windows
(`posMap`) are zero, its prescribed inverse restricts to an entrywise inverse of the
cap window `[Dx; rowP n]_(n < H)` of the surviving central entry. The principal
entry and every finite inverse column are the literal entries of `inv posMap`.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
open CategoryTheory
variable {C : Type*} [Category C] [Preadditive C]

/-- Remove the two zero pure corners from the inverse of the positive two-sector
matrix, keeping its literal surviving principal and every finite inverse column. -/
theorem posMap_isCapInverse_of_zero_corners
    {XR YR XP YP O : C} (sR : XR ⟶ YR) (sP : XP ⟶ YP)
    (Cx : XR ⟶ YP) (Dx : XP ⟶ YR) (vR : ℕ → (XR ⟶ O))
    {H : ℕ} (rowP : Fin H → (XP ⟶ O))
    (hXR : Limits.IsZero XR) (hYP : Limits.IsZero YP)
    [IsIso (posMap sR sP Cx Dx vR rowP)] :
    IsCapInverse Dx rowP
      (inv (posMap sR sP Cx Dx vR rowP) none (some none))
      (fun n => inv (posMap sR sP Cx Dx vR rowP) (some (some n)) (some none)) := by
  let M := posMap sR sP Cx Dx vR rowP
  have hsR : sR = 0 := hXR.eq_of_src _ _
  have hsP : sP = 0 := hYP.eq_of_tgt _ _
  have hvR : ∀ n, vR n = 0 := fun _ => hXR.eq_of_src _ _
  let b := inv M
  change IsCapInverse Dx rowP (b none (some none)) (fun n => b (some (some n)) (some none))
  have hleft (i j : (tObj XR XP O Empty).ι) :
      (M ≫ b) i j = (𝟙 (tObj XR XP O Empty)) i j :=
    congrArg (fun f => f i j) (IsIso.hom_inv_id M)
  have hright (i j : (tObj YR YP O (Fin H)).ι) :
      (b ≫ M) i j = (𝟙 (tObj YR YP O (Fin H))) i j :=
    congrArg (fun f => f i j) (IsIso.inv_hom_id M)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [M, Mat_.comp_apply, Fintype.sum_option, posMap, tMap, hsR, hvR,
      Pi.zero_apply, Limits.comp_zero, zero_add, Finset.sum_const_zero, add_zero, Mat_.id_apply_self] using
      hright none none
  · intro n
    have h := hright (some (some n)) none
    rw [Mat_.id_apply_of_ne _ _ _ (by simp)] at h
    simpa only [M, Mat_.comp_apply, Fintype.sum_option, posMap, tMap, hsR, hvR,
      Pi.zero_apply, Limits.comp_zero, zero_add, Finset.sum_const_zero, add_zero] using h
  · intro m
    have h := hright none (some (some m))
    rw [Mat_.id_apply_of_ne _ _ _ (by simp)] at h
    simpa only [M, Mat_.comp_apply, Fintype.sum_option, posMap, tMap, hsR, hvR,
      Pi.zero_apply, Limits.comp_zero, zero_add, Finset.sum_const_zero, add_zero] using h
  · intro n m
    have h := hright (some (some n)) (some (some m))
    by_cases hnm : n = m
    · subst m
      simpa only [M, Mat_.comp_apply, Fintype.sum_option, posMap, tMap, hsR, hvR,
        Pi.zero_apply, Limits.comp_zero, zero_add, Finset.sum_const_zero, add_zero, Mat_.id_apply_self,
        ite_true] using h
    · rw [Mat_.id_apply_of_ne _ _ _ (by simpa using hnm)] at h
      simpa only [M, Mat_.comp_apply, Fintype.sum_option, posMap, tMap, hsR, hvR,
        Pi.zero_apply, Limits.comp_zero, zero_add, Finset.sum_const_zero, add_zero, ite_eq_right hnm] using h
  · have h := hleft (some none) (some none)
    simp only [M, Mat_.comp_apply, Fintype.sum_option, posMap, tMap, hsP,
      Limits.zero_comp, Mat_.id_apply_self] at h
    rw [← h]
    change Dx ≫ b none (some none) + ∑ n, rowP n ≫ b (some (some n)) (some none) = _
    simp only [M, b, posMap, hsP, zero_add]

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
