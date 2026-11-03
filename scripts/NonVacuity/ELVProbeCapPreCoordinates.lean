import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVProbeCapPreCoordinates
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev R := ProbeVacuumCap.modulePiCategory D Sc m
private abbrev H : R ⟶ R := PiSCat.piHom R
private abbrev N := probeOldVacuumRegular D Sc m

example (i : Bool) :
    ProbeVacuumCap.shiftedPreCap D Sc m R i (positive i) H ∈ parity (R := ℚ) _ _ 0 :=
  ProbeVacuumCap.shiftedPreCap_mem D Sc m R i (positive i) H

example (i : Bool) (a : ℕ) (ha : a < probeCutoff D m i) :
    (ProbeVacuumCap.shiftedPreUnit D Sc m R i H ≫
      ProbeVacuumCap.coordinatePreDotPower D Sc m R i H a) ≫
      ProbeVacuumCap.shiftedPreCap D Sc m R i (positive i) H =
        if a + 1 = probeCutoff D m i then 𝟙 (H.obj N) else 0 :=
  ProbeVacuumCap.shiftedPreCap_dot_unit D Sc m R i (positive i) H a ha

example (i : Bool) (a : ℕ) :
    ProbeVacuumCap.coordinatePreDotPower D Sc m R i H a =
      ProbeVacuumCap.coordinatePreDotPower D Sc m R i H 1 ^ a :=
  ProbeVacuumCap.coordinatePreDotPower_eq D Sc m R i H a

example (i : Bool) :
    (ProbeVacuumCap.coordinatePreDotPower D Sc m R i H 1 ^ 2 + 1) ^ m i = 0 :=
  ProbeVacuumCap.coordinatePreDot_odd_polynomial D Sc m R i (by cases i <;> rfl) H
end NonVacuity.ELVProbeCapPreCoordinates
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
