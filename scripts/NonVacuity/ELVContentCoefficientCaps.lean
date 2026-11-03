import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientCaps
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionRows
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVContentCoefficientCaps
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev N := probeOldVacuumRegular D Sc m
private abbrev s := probeOldVacuumObject D Sc m
private theorem height (i : Bool) :
    0 ≤ contentCrossingHeight D (probeCutoff D m) i (([] : List Bool) : Multiset Bool) := by
  simp [contentCrossingHeight]
private def top (i : Bool) :
    Fin (contentUnitCount D (probeCutoff D m) i (([] : List Bool) : Multiset Bool)) :=
  ⟨probeCutoff D m i - 1, by rw [VacuumCoefficient.count]; have hp := positive i; omega⟩
example (i : Bool) : Function.Surjective
    ((contentCoefficientCap D Sc (probeCutoff D m) [] i N (height i) (top i)).total s) :=
  contentCoefficientCap_total_surjective D Sc (probeCutoff D m) [] i N (height i) (top i) s
example (i : Bool) :
    contentCoefficientCap D Sc (probeCutoff D m) [] i N (height i) (top i) ∈
      parity (R := ℚ) _ _ ((top i).val • D.parity i) :=
  contentCoefficientCap_mem D Sc (probeCutoff D m) [] i N (height i) (top i)
end NonVacuity.ELVContentCoefficientCaps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientCaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
