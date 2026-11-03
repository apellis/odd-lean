import OddMath.QuiverHecke.CyclotomicAction.ELVContentVacuumCapWindow
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVContentVacuumCapWindow
private theorem identity_ne_zero_of_vector
    {k C : Type} [CommRing k] [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) (hb : b ≠ 0) : (𝟙 s : s ⟶ s) ≠ 0 := by
  intro h
  have hi : M.map (𝟙 s) = 𝟙 (M.obj s) := M.toFunctor.map_id s
  have hz : M.map (0 : s ⟶ s) = 0 := M.toFunctor.map_zero s s
  have he := congrArg (fun f => M.map f b) h
  rw [hi, hz, SVec.id_apply, SVec.zero_apply] at he
  exact hb he

private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m (i : Bool) : ℕ := if i then 2 else 3
private abbrev cut := probeCutoff D m
private abbrev w : OldContentCategory D Sc cut [] :=
  OldContentCategory.mk (OldCategory.mk []) (List.Perm.refl [])
private def N := (restriction (oldContentInclusion D Sc cut [])).obj
  (oldRepresentable D Sc cut (OldCategory.mk []))
private def ground : N.obj w := 𝟙 (OldCategory.mk [] : OldCategory D Sc cut)
private theorem ground_ne_zero : ground ≠ 0 := by
  have h := identity_ne_zero_of_vector (probeOldVacuumRegular D Sc m) w
    (probeOldVacuumVector D Sc m) (probeOldVacuumVector_ne_zero D Sc m)
  exact h
private theorem positive (i : Bool) : 0 < cut i := by cases i <;> decide
private theorem height (i : Bool) : 0 ≤ contentCrossingHeight D cut i (0 : Multiset Bool) := by
  simp [contentCrossingHeight]
private def top (i : Bool) : Fin (contentUnitCount D cut i (0 : Multiset Bool)) :=
  ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- The input is a full old representable restricted to empty content;
no scalar-evaluation hypothesis is given. Both moving parities occur. -/
example (i : Bool) (r : Fin (contentUnitCount D cut i (0 : Multiset Bool)))
    (a : ℕ) (ha : a < contentUnitCount D cut i (0 : Multiset Bool)) (b : N.obj w) :
    (contentCoefficientCap D Sc cut [] i N (height i) r).total w
      (unitDotLinear (oldContentAppend D Sc cut [] i)
        (oldContentAppendDot_supernatural D Sc cut [] i) N a w b) =
      if a = r.val then b else 0 :=
  contentVacuumCoefficientCap_unitDot D Sc cut N i w r a ha b

/-- The last cap extracts a nonzero full-coefficient ground vector. -/
example (i : Bool) :
    (contentCoefficientCap D Sc cut [] i N (height i) (top i)).total w
      (unitDotLinear (oldContentAppend D Sc cut [] i)
        (oldContentAppendDot_supernatural D Sc cut [] i) N (cut i - 1) w ground) ≠ 0 := by
  have h := contentVacuumCoefficientCap_unitDot D Sc cut N i w (top i) (cut i - 1)
    (by rw [VacuumCoefficient.count]; exact Nat.sub_lt (positive i) (by decide)) ground
  rw [ite_eq_left rfl] at h
  exact h ▸ ground_ne_zero
end NonVacuity.ELVContentVacuumCapWindow
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentVacuumCapWindow
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
