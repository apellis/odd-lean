import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirWindowInverseData

/-! # The inverse window at the two absent vacuum corners

SwappedVacuumNonpositiveBubbles §1, equation (2): the prescribed inverse
of the negative two-sector matrix restricts to a unit-window inverse
when its reservoir source and probe target are zero. Its finite rows
are retained exactly; changing the sign of the surviving principal
changes only the inverse principal. This is the normalization needed
before coefficient-extraction identifies the extreme inverse cap.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
open CategoryTheory
variable {C : Type*} [Category C] [Preadditive C]

/-- Remove the two zero pure corners from the inverse matrix, keeping
its literal surviving principal and every finite inverse row. -/
theorem negMap_isCupInverse_of_zero_corners
    {XR YR XP YP O : C} (sR : XR ⟶ YR) (sP : XP ⟶ YP)
    (Cx : XR ⟶ YP) (Dx : XP ⟶ YR) (uR : ℕ → (O ⟶ YR))
    {G : ℕ} (colP : Fin G → (O ⟶ YP))
    (hXR : Limits.IsZero XR) (hYP : Limits.IsZero YP)
    [IsIso (negMap sR sP Cx Dx uR colP)] :
    IsCupInverse Dx (fun n : Fin G => uR n)
      (inv (negMap sR sP Cx Dx uR colP) none (some none))
      (fun n => inv (negMap sR sP Cx Dx uR colP) none (some (some n))) := by
  let M := negMap sR sP Cx Dx uR colP
  have hsR : sR = 0 := hXR.eq_of_src _ _
  have hsP : sP = 0 := hYP.eq_of_tgt _ _
  have hcol : ∀ n, colP n = 0 := fun _ => hYP.eq_of_tgt _ _
  let b := inv M
  change IsCupInverse Dx (fun n : Fin G => uR n)
    (b none (some none)) (fun n => b none (some (some n)))
  have hleft (i j : (tObj XR XP O (Fin G)).ι) :
      (M ≫ b) i j = (𝟙 (tObj XR XP O (Fin G))) i j :=
    congrArg (fun f => f i j) (IsIso.hom_inv_id M)
  have hright (i j : (tObj YR YP O Empty).ι) :
      (b ≫ M) i j = (𝟙 (tObj YR YP O Empty)) i j :=
    congrArg (fun f => f i j) (IsIso.inv_hom_id M)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [M, Mat_.comp_apply, Fintype.sum_option, Fintype.sum_empty,
      negMap, tMap, hsP, Limits.zero_comp, add_zero, Mat_.id_apply_self] using
      hleft (some none) (some none)
  · intro n
    have h := hleft (some none) (some (some n))
    rw [Mat_.id_apply_of_ne _ _ _ (by simp)] at h
    simpa only [M, Mat_.comp_apply, Fintype.sum_option, Fintype.sum_empty,
      negMap, tMap, hsP, Limits.zero_comp, add_zero] using h
  · intro n
    have h := hleft (some (some n)) (some none)
    rw [Mat_.id_apply_of_ne _ _ _ (by simp)] at h
    simpa only [M, Mat_.comp_apply, Fintype.sum_option, Fintype.sum_empty,
      negMap, tMap, hcol, Limits.zero_comp, add_zero] using h
  · intro n m
    have h := hleft (some (some n)) (some (some m))
    by_cases hnm : n = m
    · subst m
      simpa only [M, Mat_.comp_apply, Fintype.sum_option, Fintype.sum_empty,
        negMap, tMap, hcol, Limits.zero_comp, add_zero, Mat_.id_apply_self, ite_true] using h
    · rw [Mat_.id_apply_of_ne _ _ _ (by simpa using hnm)] at h
      simpa only [M, Mat_.comp_apply, Fintype.sum_option, Fintype.sum_empty,
        negMap, tMap, hcol, Limits.zero_comp, add_zero, ite_eq_right hnm] using h
  · simpa only [M, Mat_.comp_apply, Fintype.sum_option, negMap, tMap,
      hsR, Limits.comp_zero, zero_add, Mat_.id_apply_self] using hright none none

/-- The specified inverse of the negative augmented principal determines
a positive-principal unit inverse with the same finite cap rows. -/
def negMapCupInverseData
    {XR YR XP YP O : C} (sR : XR ⟶ YR) (sP : XP ⟶ YP)
    (Cx : XR ⟶ YP) (Dx : XP ⟶ YR) (uR : ℕ → (O ⟶ YR))
    {G : ℕ} (colP : Fin G → (O ⟶ YP))
    (hXR : Limits.IsZero XR) (hYP : Limits.IsZero YP)
    [IsIso (negMap (-sR) (-sP) (-Cx) (-Dx) uR colP)] :
    CupInverseData Dx (fun n : Fin G => uR n) where
  principal := -inv (negMap (-sR) (-sP) (-Cx) (-Dx) uR colP) none (some none)
  window n := inv (negMap (-sR) (-sP) (-Cx) (-Dx) uR colP) none (some (some n))
  isInverse := by
    simpa only [neg_neg] using
      (negMap_isCupInverse_of_zero_corners (-sR) (-sP) (-Cx) (-Dx) uR colP hXR hYP).neg_principal

omit [Preadditive C] in

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
