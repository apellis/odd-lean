import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightNegativeCap
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open ELVOld CyclotomicAction
namespace NonVacuity.ELVProbeWeightNegativeCap
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem hc (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private def muP (i : Bool) : Bool → ℤ := Λ - D.α i
private theorem edge (i : Bool) : -Λ + D.α i = -muP i := by unfold muP; abel
private abbrev R := ProbeVacuumCap.modulePiCategory D Sc m
private def W (_ : Bool → ℤ) := R
private def H : R ⟶ R := 𝟙 R
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
example (i : Bool) (n : ℕ) :=
  WeightTensorVacuum.vacuumPreInverseDot_source D Sc m Λ hc W 0 i (edge i) H (positive i) rfl n
example (i : Bool) (n : ℕ) :=
  WeightTensorVacuum.vacuumPreNegativeCap_native D Sc m Λ hc W 0 i (edge i) H (positive i) rfl n
example (i : Bool) := ProbeVacuumCap.shiftedPreDot_odd_polynomial D Sc m R i rfl H
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m
private theorem shifted_cap_nonzero (i : Bool) :
    ProbeVacuumCap.shiftedPreCap D Sc m R i (positive i) H ≠ 0 := by
  intro hz
  have hw := ProbeVacuumCap.shiftedPreCap_dot_unit D Sc m R i (positive i) H
    (probeCutoff D m i - 1) (by have hp := positive i; omega)
  rw [hz, Limits.comp_zero, ite_eq_left (by have hp := positive i; omega)] at hw
  have he := congrArg (fun f : End (probeOldVacuumRegular D Sc m) =>
    f.total (probeOldVacuumObject D Sc m) (probeOldVacuumVector D Sc m)) hw
  change (0 : End (probeOldVacuumRegular D Sc m)).total
      (probeOldVacuumObject D Sc m) (probeOldVacuumVector D Sc m) =
    (𝟙 (probeOldVacuumRegular D Sc m) : End (probeOldVacuumRegular D Sc m)).total
      (probeOldVacuumObject D Sc m) (probeOldVacuumVector D Sc m) at he
  simp only [SuperNatTrans.total, Superfunctor.zero_app, Superfunctor.id_app_zero,
    Superfunctor.id_app_one, add_zero] at he
  exact probeOldVacuumVector_ne_zero D Sc m he.symm
example (i : Bool) : ProbeVacuumCap.shiftedPreCap D Sc m R i (positive i) H ≠ 0 :=
  shifted_cap_nonzero i
end NonVacuity.ELVProbeWeightNegativeCap
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightNegativeCap
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations"
