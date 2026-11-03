import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-! Scope tests for actual word induction of the regular full-coefficient
power quotient. Occupied bounded-word detection is subsequent work.
-/
noncomputable section
namespace NonVacuity.ELVPowerWordCoordinates
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 6
private def L (_ : Bool × ℕ) : ℕ := 3
private def ν : List Bool := [false, true]

example (w : OldCategory D Sc cutoff) :
    Function.Surjective (powerWordGenerator D Sc cutoff L ν w) :=
  powerWordGenerator_surjective D Sc cutoff L ν w

example (w : OldCategory D Sc cutoff) :
    LinearMap.ker (powerWordGenerator D Sc cutoff L ν w) =
      powerWordRelationSpan D Sc cutoff L ν w := powerWordGenerator_ker D Sc cutoff L ν w

example : powerWordModule D Sc cutoff L [] = coefficientPowerVacuum D Sc cutoff L :=
  powerWordModule_nil D Sc cutoff L

example (i : Bool) := powerWordAppendIso D Sc cutoff L ν i

example (w : OldCategory D Sc cutoff) :=
  powerWordRelationSpan_le_elementaryPowerImage D Sc cutoff L ν w

end NonVacuity.ELVPowerWordCoordinates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoordinates
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
