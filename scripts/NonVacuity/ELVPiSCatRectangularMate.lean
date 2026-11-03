import OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRectangularMate
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace PiSCatRectangularMateConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := AsymmetricParameters.datum
private def Sc : SKM.Scalars D ℚ := AsymmetricParameters.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev hJ : (0 : Bool → ℤ) + D.α true = D.α true := zero_add _
private abbrev hI : (0 : Bool → ℤ) + D.α false = D.α false := zero_add _
private abbrev hUp : D.α true + D.α false = D.α true + D.α false := rfl
private abbrev hOther : D.α false + D.α true = D.α true + D.α false := add_comm _ _
private abbrev A₁ := elvActionAdjunction D Sc cut 8 true 0 hJ
private abbrev A₃ := elvActionAdjunction D Sc cut 8 true 0 hOther
private abbrev g := elvE D Sc cut 8 false 0 hI
private abbrev h := elvE D Sc cut 8 false 0 hUp
private abbrev z := elvActionCross D Sc cut 8 true false 0 hI hOther hJ hUp
private def M : ELVWeightProduct D Sc cut 8 0 (D.α true) := fun δ =>
  (BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[true]⟩))

/-- Two distinct odd colours use the selected crossing and j-adjunctions at different weights. -/
example (r : ZMod 2) := SKM.rectangularMate_piscat_app A₁ A₃ g h z
  (fun W => Superfunctor.app_eq_zero_of_mem A₃.unit_mem (by decide) W)
  (fun W => Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide) W) r M
example := SKM.rectangularMate_piscat_mem A₁ A₃ g h z
  (elvActionCross_mem D Sc cut 8 true false 0 hI hOther hJ hUp)
example : D.parity false * D.parity true = 1 := by decide
end PiSCatRectangularMateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRectangularMate
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
