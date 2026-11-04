import OddMath.QuiverHecke.CyclotomicAction.ELVContentHomZero
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace ContentHomZeroConsumer
local instance homPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def cutoff : Bool → ℕ := fun _ => 4

-- A nonempty content and any whole probe category require no extra zero-object hypothesis.
example (A : PiSCat.{0,0,1} ℚ) :
    Limits.IsZero (contentHomZero D Sc cutoff 12 ([true, false] : List Bool) A) :=
  contentHomZero_isZero D Sc cutoff 12 _ A
example (A : PiSCat.{0,0,1} ℚ) :
    Limits.HasZeroObject (A ⟶ contentModuleTarget
      D Sc cutoff 12 ([true, false] : List Bool)) := inferInstance
end ContentHomZeroConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentHomZero
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"
