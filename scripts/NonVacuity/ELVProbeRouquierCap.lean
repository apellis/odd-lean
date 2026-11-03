import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierCap
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace NonVacuity.ELVProbeRouquierCap
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev N := probeOldVacuumRegular D Sc m
private abbrev K (i : Bool) := oldContentAppend D Sc (probeCutoff D m) [] i

/-- The given right-adjunction fields agree for every actual native dot power. -/
example (i : Bool) (a : ℕ) :
    ((ProbeVacuumCap.appendRightAdjunction D Sc m i).unit ≫
      SKM.rouquierPower (ProbeVacuumCap.inductionDotCell D Sc m i) a ▷
        ProbeVacuumCap.restrictionCell D Sc m i).total N =
      unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a :=
  ProbeVacuumCap.appendRightUnitPower_total D Sc m i a

/-- On both occupied odd probes the native normalization factor is minus. -/
example (i : Bool) :
    koszulSign ((probeCutoff D m i - 1) • D.parity i) ((probeCutoff D m i - 1) • D.parity i) •
      ProbeVacuumCap.cap D Sc m i (positive i) = -ProbeVacuumCap.cap D Sc m i (positive i) := by
  have hs : koszulSign ((probeCutoff D m i - 1) • D.parity i)
      ((probeCutoff D m i - 1) • D.parity i) = -1 := by cases i <;> rfl
  rw [hs, neg_one_zsmul]

example (i : Bool) :
    koszulSign ((probeCutoff D m i - 1) • D.parity i) ((probeCutoff D m i - 1) • D.parity i) •
      (koszulSign ((probeCutoff D m i - 1) • D.parity i) ((probeCutoff D m i - 1) • D.parity i) •
        ProbeVacuumCap.cap D Sc m i (positive i)) = ProbeVacuumCap.cap D Sc m i (positive i) :=
  koszulSign_smul_smul _ _ _

example (i : Bool) : ProbeVacuumCap.cap D Sc m i (positive i) ≠ 0 :=
  ProbeVacuumCap.cap_ne_zero D Sc m i (positive i)

section SuppliedLocalInput
variable (i : Bool) {A : PiSCat.{0,0,1} ℚ}
  {E₀ : A ⟶ ProbeVacuumCap.modulePiCategory D Sc m}
  {F₀ : ProbeVacuumCap.modulePiCategory D Sc m ⟶ A}
  (A₀ : SKM.SuperAdjunction (k := ℚ) E₀ F₀) (x₀ : End E₀)
  (t : End (E₀ ≫ ProbeVacuumCap.inductionCell D Sc m i))
  (L : SKM.SuperRouquierLoc A₀ (ProbeVacuumCap.appendRightAdjunction D Sc m i)
    x₀ (ProbeVacuumCap.inductionDotCell D Sc m i) t (D.parity i)
      (-((probeCutoff D m i : ℕ) : ℤ)))

/-- The local record is supplied input data, not constructed by this
consumer. No row-identification or left-triangle hypothesis is assumed. -/
example : (ProbeVacuumCap.localCapFamily D Sc m i A₀ x₀ t L).total N =
    ProbeVacuumCap.cap D Sc m i (positive i) :=
  ProbeVacuumCap.local_capL_total D Sc m i A₀ x₀ t L (positive i)
end SuppliedLocalInput
end NonVacuity.ELVProbeRouquierCap
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierCap
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
