import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPrecomposition
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace NonVacuity.ELVProbeCapPrecomposition
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev R := ProbeVacuumCap.modulePiCategory D Sc m
private abbrev H : R ⟶ R := PiSCat.piHom R
private abbrev N := probeOldVacuumRegular D Sc m
private abbrev K (i : Bool) := oldContentAppend D Sc (probeCutoff D m) [] i

/-- The chosen reservoir is the actual parity functor on native modules;
its action on odd maps is retained in the equality. -/
example (i : Bool) :
    ((ProbeVacuumCap.preCap D Sc m R i (positive i)).total H).total N =
      H.map (ProbeVacuumCap.cap D Sc m i (positive i)) :=
  ProbeVacuumCap.preCap_total D Sc m R i (positive i) H

example (i : Bool) :
    ProbeVacuumCap.preDotEnd D Sc m R i H = H.map (ProbeVacuumCap.moduleDot D Sc m i) :=
  ProbeVacuumCap.preDotEnd_eq D Sc m R i H

example (i : Bool) (a : ℕ) (ha : a < probeCutoff D m i) :
    (H.map ((adjunction (K i)).unit.app N) ≫ ProbeVacuumCap.preDotEnd D Sc m R i H ^ a) ≫
      ((ProbeVacuumCap.preCap D Sc m R i (positive i)).total H).total N =
        if a + 1 = probeCutoff D m i then 𝟙 (H.obj N) else 0 :=
  ProbeVacuumCap.preCap_dot_unit D Sc m R i (positive i) H a ha

example (i : Bool) :
    (ProbeVacuumCap.preDotEnd D Sc m R i H ^ 2 + 1) ^ m i = 0 :=
  ProbeVacuumCap.preDot_odd_polynomial D Sc m R i (by cases i <;> rfl) H

example (i : Bool) : ProbeVacuumCap.capCell D Sc m i (positive i) ∈
    parity (R := ℚ) _ _ 1 := by
  have h := ProbeVacuumCap.capCell_mem D Sc m i (positive i)
  convert h using 1; cases i <;> rfl
end NonVacuity.ELVProbeCapPrecomposition
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPrecomposition
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
