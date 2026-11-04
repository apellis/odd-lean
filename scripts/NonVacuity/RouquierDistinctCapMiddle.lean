import OddMath.SKM.RouquierDistinctCapMiddle
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCapMiddle
private abbrev disconnected := AsymmetricParameters.datum
private abbrev ds := AsymmetricParameters.scalars
private def m : Bool → ℕ := fun _ => 3
private def Λ : Bool → ℤ := fun i => probeCutoff disconnected m i
private theorem cutoff (i : Bool) : (probeCutoff disconnected m i : ℤ) = disconnected.h i Λ := rfl
private abbrev T := probeOldRouquierFamily disconnected (parameterTwist disconnected ds) m Λ cutoff
private theorem M : RouquierMulticolour T ds := probeOldRouquierMulticolour disconnected ds m Λ cutoff
private def b (i : Bool) : Bool → ℤ := -Λ + 4 • disconnected.α i
private def a (i : Bool) : Bool → ℤ := b i - disconnected.α i
private theorem hab (i : Bool) : a i + disconnected.α i = b i := sub_add_cancel _ _
private theorem hfc (i : Bool) : (a i + disconnected.α (!i)) + disconnected.α i =
    b i + disconnected.α (!i) := by rw [a]; abel
private theorem hed (i : Bool) : (b i + disconnected.α i) + disconnected.α (!i) =
    (b i + disconnected.α (!i)) + disconnected.α i := by abel
private theorem ne (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem positive : 0 < disconnected.h true (b true) := by
  norm_num [b, Λ, m, disconnected, Datum.h, Datum.α, AsymmetricParameters.datum,
    probeCutoff, probeDotExponent]
private theorem middle : disconnected.h true (b true) < disconnected.d true false := by
  norm_num [b, Λ, m, disconnected, Datum.h, Datum.α, Datum.d, AsymmetricParameters.datum,
    probeCutoff, probeDotExponent]
example := T.distinctMixedBraidLeft_cap_middle M (ne true)
  (hab true) rfl rfl rfl (hfc true) rfl (hed true) positive middle
example (i : Bool) : probeOldVacuumAppendVector disconnected
    (parameterTwist disconnected ds) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero disconnected (parameterTwist disconnected ds) m i
    (by cases i <;> decide)
end NonVacuity.RouquierDistinctCapMiddle
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCapMiddle
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty audit"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
