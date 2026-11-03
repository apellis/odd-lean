import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCoefficientCapUniqueness
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVProbeCoefficientCapUniqueness
private theorem module_epi_ne_zero
    {k C : Type} [CommRing k] [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (hs : ∀ w, Function.Surjective (f.total w)) (hid : (𝟙 N : N ⟶ N) ≠ 0) : f ≠ 0 := by
  intro hf
  apply hid
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  have hi : (𝟙 N : N ⟶ N).total w = 𝟙 (N.obj w) := SuperNatTrans.id_total N.toFunctor w
  rw [hi]
  simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]
  apply SVec.hom_ext
  intro b
  obtain ⟨a, ha⟩ := hs w b
  have hz : f.total w a = 0 := by
    rw [hf]
    simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, SVec.zero_apply]
  simpa only [SVec.id_apply, SVec.zero_apply] using ha.symm.trans hz

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev N := probeOldVacuumRegular D Sc m
private abbrev K (i : Bool) := oldContentAppend D Sc (probeCutoff D m) [] i
private abbrev s := probeOldVacuumObject D Sc m
private def FE (i : Bool) := ProbeVacuumCap.source D Sc m i
private theorem evaluates (i : Bool) : ProbeEvaluatesCoefficients D m Sc [] (FE i) :=
  probeOldRestriction_evaluatesCoefficients D Sc m [] i ((induction (K i)).obj N)
    (probeOldInduced_evaluatesCoefficients D m Sc [] i N
      (probeOldModule_evaluatesCoefficients D m Sc [] _))

private theorem height (i : Bool) : 0 ≤ contentCrossingHeight D (probeCutoff D m) i (0 : Multiset Bool) := by
  simp [contentCrossingHeight]
private def row (i : Bool) (r : Fin (contentUnitCount D (probeCutoff D m) i (0 : Multiset Bool))) :=
  contentCoefficientCap D Sc (probeCutoff D m) [] i (FE i) (height i) r

/-- The criterion applies at F(E(T0)), with its scalar-evaluation condition
proved by actual induction/restriction closure. Every column premise is
supplied by the existing given coefficient cap window. -/
example (i : Bool) (r : Fin (contentUnitCount D (probeCutoff D m) i (0 : Multiset Bool))) :
    𝟙 ((restriction (K i)).obj ((induction (K i)).obj (FE i))) ≫ row i r = row i r := by
  apply probeContentCoefficientCap_eq_of_window D Sc m [] (FE i) (evaluates i) i (by simp) r
  intro w a ha
  rw [Category.id_comp]
  exact probeContentCoefficientCap_unitDot D Sc m [] (FE i) (evaluates i) i (by simp) w r a ha

/-- The occupied source of the original nonzero native cap remains nonzero. -/
private theorem occupiedFE (i : Bool) : (𝟙 (FE i) : FE i ⟶ FE i) ≠ 0 := by
  intro hid
  apply ProbeVacuumCap.cap_ne_zero D Sc m i (positive i)
  calc
    ProbeVacuumCap.cap D Sc m i (positive i) =
      (𝟙 (FE i)) ≫ ProbeVacuumCap.cap D Sc m i (positive i) := (Category.id_comp _).symm
    _ = 0 := by rw [hid, Limits.zero_comp]

/-- The second-level native cap is nonzero on the occupied F/E probe. -/
example (i : Bool) (r : Fin (contentUnitCount D (probeCutoff D m) i (0 : Multiset Bool))) :
    row i r ≠ 0 :=
  module_epi_ne_zero (row i r)
    (contentCoefficientCap_total_surjective D Sc (probeCutoff D m) [] i (FE i) (height i) r)
    (occupiedFE i)
end NonVacuity.ELVProbeCoefficientCapUniqueness
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCoefficientCapUniqueness
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
