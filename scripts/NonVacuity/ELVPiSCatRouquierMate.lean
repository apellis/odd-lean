import OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace PiSCatRouquierMateConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private theorem lower (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private theorem upper (i : Bool) : D.α i + D.α i = D.α i + D.α i := rfl
private def M (i : Bool) : ELVWeightProduct D Sc cut 8 0 (D.α i) := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[i]⟩)))
/-- The prescribed signed equal-colour crossing is used at both parities. -/
example (i : Bool) (p : ZMod 2) := SKM.rouquierMate_piscat_app
  (elvActionAdjunction D Sc cut 8 i 0 (lower i)) (elvActionAdjunction D Sc cut 8 i 0 (upper i))
  (elvActionCross D Sc cut 8 i i 0 (lower i) (upper i) (lower i) (upper i)) p (M i)
example (i : Bool) := SKM.rouquierMate_piscat_eq_rectangular
  (elvActionAdjunction D Sc cut 8 i 0 (lower i)) (elvActionAdjunction D Sc cut 8 i 0 (upper i))
  (elvActionCross D Sc cut 8 i i 0 (lower i) (upper i) (lower i) (upper i))
end PiSCatRouquierMateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRouquierMate
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
