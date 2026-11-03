import OddMath.SKM.RouquierZeroLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.RouquierZeroLocal
private theorem identity_ne_zero_of_vector
    {k C : Type} [CommRing k] [Category.{0} C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) (hb : b ≠ 0) : (𝟙 s : s ⟶ s) ≠ 0 := by
  intro h
  have hi : M.map (𝟙 s) = 𝟙 (M.obj s) := M.toFunctor.map_id s
  have hz : M.map (0 : s ⟶ s) = 0 := M.toFunctor.map_zero s s
  have he := congrArg (fun f => M.map f b) h
  rw [hi, hz, SVec.id_apply, SVec.zero_apply] at he
  exact hb he
private theorem inverse_column_apply
    {k C : Type} [CommRing k] [Category.{0} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {M T : Superfunctor k C (SVec k)} (u : M ⟶ T) (v : T ⟶ M) (h : u ≫ v = 𝟙 M)
    (w : C) (b : M.obj w) : v.total w (u.total w b) = b := by
  have he := congrArg (fun f : M ⟶ M => f.total w b) h
  rw [Superfunctor.comp_total, SVec.comp_apply] at he
  have hi : (𝟙 M : M ⟶ M).total w = 𝟙 (M.obj w) := SuperNatTrans.id_total M.toFunctor w
  rw [hi, SVec.id_apply] at he
  exact he
private theorem boundary_cap_nonzero
    {k C A : Type} [CommRing k] [Category.{0} C] [Category.{0} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α) (m : ℕ)
    (e : ∀ M, OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ≅
      (restriction J).obj ((induction J).obj M))
    (he : ∀ M, (e M).hom = unitColumnModuleMap J hα M m) (hm : 0 < m)
    (M : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) (hb : b ≠ 0) :
    (((inductionVacuumCoefficients J hα m e he).cap).total M).total w
      ((unitDotColumn J hα M (m - 1)).total w b) ≠ 0 := by
  have h := (inductionVacuumCoefficients J hα m e he).cup_cap hm (j := m - 1) (by omega)
  rw [ite_eq_left rfl, inductionModuleUnitPower_eq] at h
  have hM := congrArg
    (fun f : (𝟙 (inductionModulePiCategory (k := k) C)) ⟶
      (𝟙 (inductionModulePiCategory (k := k) C)) => f.total M) h
  rw [Superfunctor.comp_total, gridUnitColumnTransformation_total] at hM
  have hi : (𝟙 (Superfunctor.id k (Superfunctor k C (SVec k))) :
      End (Superfunctor.id k (Superfunctor k C (SVec k)))).total M = 𝟙 M :=
    SuperNatTrans.id_total (𝟭 (Superfunctor k C (SVec k))) M
  erw [hi] at hM
  have hx := inverse_column_apply _ _ hM w b
  erw [hx]
  exact hb
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m (i : Bool) : ℕ := if i then 2 else 3
private abbrev cut := probeCutoff D m
private def localFrom (cutoff : Bool → ℕ) (γ : List Bool) (i : Bool) (hi : i ∉ γ) :=
  SKM.RouquierZeroLocal.ofCoefficients
    (zeroModuleCellAdjunction (k := ℚ) (OldContentCategory D Sc cutoff γ))
    (inductionModuleAdjunction (k := ℚ) (oldContentAppend D Sc cutoff γ i))
    (inductionModuleDot (oldContentAppend D Sc cutoff γ i)
      (oldContentAppendDot_supernatural D Sc cutoff γ i)) (D.parity i)
    (contentUnitCount D cutoff i (γ : Multiset Bool))
    (contentMissingBoundaryCoefficients D Sc cutoff γ i hi)
    (zeroModuleCell_comp_id (OldContentCategory D Sc cutoff γ)
      (inductionModulePiCategory (k := ℚ) (OldContentCategory D Sc cutoff γ))
      (zeroModuleCell (k := ℚ) (OldContentCategory D Sc cutoff γ)))
    (zeroModuleCell_comp_id (OldContentCategory D Sc cutoff γ)
      (inductionModulePiCategory (k := ℚ) (OldContentCategory D Sc cutoff (i :: γ)))
      (inductionModuleCell (k := ℚ) (oldContentAppend D Sc cutoff γ i)))

private abbrev w : OldContentCategory D Sc cut [] :=
  OldContentCategory.mk (OldCategory.mk []) (List.Perm.refl [])
private def N := (restriction (oldContentInclusion D Sc cut [])).obj
  (oldRepresentable D Sc cut (OldCategory.mk []))
private def ground : N.obj w := 𝟙 (OldCategory.mk [] : OldCategory D Sc cut)
private theorem ground_ne_zero : ground ≠ 0 := by
  exact identity_ne_zero_of_vector (probeOldVacuumRegular D Sc m) w
    (probeOldVacuumVector D Sc m) (probeOldVacuumVector_ne_zero D Sc m)
private def boundary (i : Bool) := contentMissingBoundaryCoefficients D Sc cut [] i (by simp)
private theorem positive (i : Bool) : 0 < cut i := by cases i <;> decide
/-- Every finite boundary identity uses the constructed given matrix, in both parities. -/
example (i : Bool) := (boundary i).total
example (i : Bool) (j l : ℕ) (hj : j < cut i) (hl : l < cut i) :=
  (boundary i).entry j l (by simpa only [VacuumCoefficient.count] using hj)
    (by simpa only [VacuumCoefficient.count] using hl)
example (i : Bool) (n : ℕ) := (boundary i).coeff_mem n
/-- The raw top boundary cap extracts a nonzero full-coefficient vector. -/
private theorem boundary_top_nonzero (i : Bool) :
    ((boundary i).cap.total N).total w
      ((unitDotColumn (oldContentAppend D Sc cut [] i)
        (oldContentAppendDot_supernatural D Sc cut [] i) N (contentUnitCount D cut i (([] : List Bool) : Multiset Bool) - 1)).total w ground) ≠ 0 := by
  exact boundary_cap_nonzero (oldContentAppend D Sc cut [] i)
    (oldContentAppendDot_supernatural D Sc cut [] i)
    (contentUnitCount D cut i (([] : List Bool) : Multiset Bool))
    (contentMissingUnitModuleIso D Sc cut [] i (by simp))
    (contentMissingUnitModuleIso_hom D Sc cut [] i (by simp))
    (by rw [VacuumCoefficient.count]; exact positive i) N w ground ground_ne_zero
/-- At zero cutoff the finite boundary remains constructed. -/
example (i : Bool) := (contentMissingBoundaryCoefficients D Sc (fun _ => 0) [] i (by simp)).total
/-- The actual empty local record is constructed, rather than supplied. -/
private def localData (i : Bool) := localFrom cut [] i (by simp)
example (i : Bool) := (localData i).dot₁_mem
example (i : Bool) := (localData i).dot₂_mem
example (i : Bool) := (localData i).cross_mem
example (i : Bool) := (localData i).slide_left
example (i : Bool) := (localData i).slide_right
example (i : Bool) := ((localData i).invNeg (by omega)).total
example (i : Bool) (j l : ℕ) (hj : j < cut i) (hl : l < cut i) :=
  ((localData i).invNeg (by omega)).gg j l (by simpa only [neg_neg, Int.toNat_natCast, VacuumCoefficient.count] using hj)
    (by simpa only [neg_neg, Int.toNat_natCast, VacuumCoefficient.count] using hl)
private theorem row_preserved (i : Bool) (j : ℕ) :
    ((localData i).invNeg (by omega)).g' j = (boundary i).coeff j := by
  exact SKM.RouquierZeroLocal.ofCoefficients_invNeg_g' _ _ _ _ _ _
    (zeroModuleCell_comp_id (OldContentCategory D Sc cut [])
      (inductionModulePiCategory (k := ℚ) (OldContentCategory D Sc cut []))
      (zeroModuleCell (k := ℚ) (OldContentCategory D Sc cut [])))
    (zeroModuleCell_comp_id (OldContentCategory D Sc cut [])
      (inductionModulePiCategory (k := ℚ) (OldContentCategory D Sc cut [i]))
      (inductionModuleCell (k := ℚ) (oldContentAppend D Sc cut [] i))) (by omega) j
example (i : Bool) :
    ((((localData i).invNeg (by omega)).g'
      (contentUnitCount D cut i (([] : List Bool) : Multiset Bool) - 1)).total N).total w
      ((unitDotColumn (oldContentAppend D Sc cut [] i)
        (oldContentAppendDot_supernatural D Sc cut [] i) N
        (contentUnitCount D cut i (([] : List Bool) : Multiset Bool) - 1)).total w ground) ≠ 0 := by
  rw [row_preserved]
  have hc : 0 < contentUnitCount D cut i (([] : List Bool) : Multiset Bool) := by
    rw [VacuumCoefficient.count]
    exact positive i
  simpa only [SKM.RouquierBoundary.Coefficients.cap, ite_eq_left hc] using boundary_top_nonzero i

-- Nonempty absent-colour content retains both moving parities.
private def other (i : Bool) : List Bool := [!i]
private theorem absent (i : Bool) : i ∉ other i := by cases i <;> decide
private def missing (i : Bool) := localFrom cut (other i) i (absent i)
private theorem missingHeight (i : Bool) :
    -(contentUnitCount D cut i (other i : Multiset Bool) : ℤ) ≤ 0 := by omega
example (i : Bool) := (missing i).slide_left
example (i : Bool) := (missing i).slide_right
example (i : Bool) := ((missing i).invNeg (missingHeight i)).total
example (i : Bool) := ((missing i).invNeg (missingHeight i)).ff
private def occupied (i : Bool) := (restriction (oldContentInclusion D Sc cut (other i))).obj
  (oldRepresentable D Sc cut (OldCategory.mk (other i)))
example (i : Bool) (n : ℕ) (hn : n < contentUnitCount D cut i (other i : Multiset Bool)) :=
  contentMissingBoundary_coefficient_total D Sc cut (other i) i (absent i) n hn (occupied i)
example (i : Bool) (n : ℕ) (hn : n < contentUnitCount D cut i (other i : Multiset Bool)) :=
  contentMissingBoundary_coefficient_total D Sc cut (other i) i (absent i) n hn
    (supermoduleParityObj (occupied i))

example : probeOldVacuumVector D Sc (fun _ : Bool => 0) ≠ 0 :=
  probeOldVacuumVector_ne_zero D Sc (fun _ : Bool => 0)

-- At height zero BOTH presentations are required, even with an odd dot.
private def zeroLocal (i : Bool) := localFrom (fun _ => 0) [] i (by simp)
example (i : Bool) := ((zeroLocal i).invPos (by simp [contentUnitCount, contentCrossingHeight])).total
example (i : Bool) := ((zeroLocal i).invPos (by simp [contentUnitCount, contentCrossingHeight])).ff
example (i : Bool) := ((zeroLocal i).invNeg (by omega)).total
example (i : Bool) := ((zeroLocal i).invNeg (by omega)).ff
end NonVacuity.RouquierZeroLocal
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.SKM.RouquierZeroLocal] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
