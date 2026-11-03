import OddMath.QuiverHecke.CyclotomicAction.ELVOldGeneratorDegrees
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace OldGeneratorDegreesConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev sy := CyclotomicAction.AsymmetricParameters.symmetrizer
private theorem homogeneous : Sc.Homogeneous := CyclotomicAction.AsymmetricParameters.homogeneous
private def cutoff (_ : Bool) : ℕ := 8
local instance : GradedSupercategory ℚ (OldCategory D Sc cutoff) :=
  oldCategoryGradedSupercategory D Sc cutoff sy homogeneous
private def mixed : OldCategory D Sc cutoff := ⟨[false,true,false]⟩
example (i : Bool) := oldAppendDotComponent_degree D Sc cutoff sy homogeneous i mixed
example (i : Bool) := equalCrossComponent_degree D Sc cutoff sy homogeneous i mixed
example : 2 * sy.d false = 4 := rfl
example : 2 * sy.d true = 2 := rfl
example : -2 * sy.d false = -4 := rfl
example : -2 * sy.d true = -2 := rfl
example : D.parity false = D.parity true := rfl
end OldGeneratorDegreesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldGeneratorDegrees
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
