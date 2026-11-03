import OddMath.QuiverHecke.CyclotomicAction.ELVOldInductionBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OldInductionBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 6
private def source (v : List Bool) : OldCategory D Sc cut := ⟨v⟩
private def R (v : List Bool) := oldRepresentable D Sc cut (source v)
private abbrev T (i : Bool) :=
  (append D Sc cut i ⋙ append D Sc cut i) ⋙ append D Sc cut i
private def vector (v : List Bool) (i : Bool) :
    ((induction (T i)).obj (R v)).obj ((T i).obj (source v)) :=
  tensor (T i) (R v).toFunctor (source v) (𝟙 _) (𝟙 (source v))

/-- Actual representable inputs, including mixed old contents and both moving parities. -/
example (i : Bool) := oldTripleCross_braid D Sc cut i (R [])
example (i : Bool) := oldTripleCross_braid D Sc cut i (R [false,true])
example (i : Bool) := oldTripleCross_braid D Sc cut i (supermoduleParityObj (R []))

/-- Evaluate the whole module braid on the literal unit tensor. -/
example (i : Bool) := congrArg
  (fun f : End ((induction (T i)).obj (R [false,true])) =>
    f.total ((T i).obj (source [false,true])) (vector [false,true] i))
  (oldTripleCross_braid D Sc cut i (R [false,true]))
end OldInductionBraidConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldInductionBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
