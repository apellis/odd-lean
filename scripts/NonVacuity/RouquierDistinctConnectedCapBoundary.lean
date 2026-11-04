import OddMath.SKM.RouquierDistinctConnectedCapBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctConnectedCapBoundary
private abbrev disconnected := AsymmetricParameters.datum
private abbrev ds := AsymmetricParameters.scalars
private def m : Bool → ℕ := fun _ => 3
private def Λ : Bool → ℤ := fun i => probeCutoff disconnected m i
private theorem cutoff (i : Bool) : (probeCutoff disconnected m i : ℤ) = disconnected.h i Λ := rfl
private abbrev T := probeOldRouquierFamily disconnected (parameterTwist disconnected ds) m Λ cutoff
private theorem M : RouquierMulticolour T ds := probeOldRouquierMulticolour disconnected ds m Λ cutoff
private def b (i : Bool) : Bool → ℤ := -Λ + 3 • disconnected.α i
private def a (i : Bool) : Bool → ℤ := b i - disconnected.α i
private theorem hab (i : Bool) : a i + disconnected.α i = b i := sub_add_cancel _ _
private theorem hfc (i : Bool) : (a i + disconnected.α (!i)) + disconnected.α i =
    b i + disconnected.α (!i) := by rw [a]; abel
private theorem hed (i : Bool) : (b i + disconnected.α i) + disconnected.α (!i) =
    (b i + disconnected.α (!i)) + disconnected.α i := by abel
private theorem ne (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem zeroHeight (i : Bool) : disconnected.h i (b i) = 0 := by
  cases i <;> norm_num [b, Λ, m, disconnected, Datum.h, Datum.α, AsymmetricParameters.datum,
    probeCutoff, probeDotExponent]
private theorem connected (i : Bool) : disconnected.d i (!i) ≠ 0 := by cases i <;> decide
example (i : Bool) := T.distinctMixedBraidLeft_cap_of_zero_connected M (ne i)
  (hab i) rfl rfl rfl (hfc i) rfl (hed i) (zeroHeight i) (connected i)
example (i : Bool) := T.distinctMixedBraidLeft_cap_of_zero M (ne i)
  (hab i) rfl rfl rfl (hfc i) rfl (hed i) (zeroHeight i)
example (i : Bool) := T.distinctCapRight_principal_of_zero M (ne i)
  (hab i) rfl rfl rfl (hed i) (zeroHeight i)
example (i : Bool) : probeOldVacuumAppendVector disconnected
    (parameterTwist disconnected ds) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero disconnected (parameterTwist disconnected ds) m i
    (by cases i <;> decide)
end NonVacuity.RouquierDistinctConnectedCapBoundary
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctConnectedCapBoundary
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty audit"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
