import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreDotSigns
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVProbeCapPreDotSigns
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev R := ProbeVacuumCap.modulePiCategory D Sc m
private abbrev H : R ⟶ R := PiSCat.piHom R
private abbrev N := probeOldVacuumRegular D Sc m

/-- Both odd probe cutoffs have a genuine negative source-comparison sign. -/
example (i : Bool) : ProbeVacuumCap.shiftedPreDot D Sc m R i H =
    -ProbeVacuumCap.coordinatePreDotPower D Sc m R i H 1 := by
  have h := ProbeVacuumCap.shiftedPreDot_coordinates D Sc m R i H
  have hs : koszulSign (D.parity i) ((probeCutoff D m i - 1) • D.parity i) = -1 := by
    cases i <;> rfl
  rw [hs, neg_one_zsmul] at h
  exact h

example (i : Bool) (a : ℕ) : ProbeVacuumCap.shiftedPreDot D Sc m R i H ^ a =
    koszulSign ((a : ZMod 2) * D.parity i) ((probeCutoff D m i - 1) • D.parity i) •
      ProbeVacuumCap.coordinatePreDotPower D Sc m R i H a :=
  ProbeVacuumCap.shiftedPreDot_power D Sc m R i H a

/-- At both cutoff 2 and cutoff 4, the last raw shifted-dot window has
negative identity, rather than unsigned identity. -/
example (i : Bool) :
    (ProbeVacuumCap.shiftedPreUnit D Sc m R i H ≫
      ProbeVacuumCap.shiftedPreDot D Sc m R i H ^ (probeCutoff D m i - 1)) ≫
      ProbeVacuumCap.shiftedPreCap D Sc m R i (positive i) H = -(𝟙 (H.obj N)) := by
  have h := ProbeVacuumCap.shiftedPreCap_rawDot_unit D Sc m R i (positive i) H
    (probeCutoff D m i - 1) (Nat.sub_lt (positive i) (by decide))
  have hs : koszulSign (((probeCutoff D m i - 1 : ℕ) : ZMod 2) * D.parity i)
      ((probeCutoff D m i - 1) • D.parity i) = -1 := by cases i <;> rfl
  rw [ite_eq_left (Nat.sub_add_cancel (positive i)), hs, neg_one_zsmul] at h
  exact h

example (i : Bool) : (ProbeVacuumCap.shiftedPreDot D Sc m R i H ^ 2 + 1) ^ m i = 0 :=
  ProbeVacuumCap.shiftedPreDot_odd_polynomial D Sc m R i (by cases i <;> rfl) H
end NonVacuity.ELVProbeCapPreDotSigns
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreDotSigns
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
