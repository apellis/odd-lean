import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace OldAppendBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 6
private def source (v : List Bool) : OldCategory D Sc cut := ⟨v⟩
private def upper (v : List Bool) (i : Bool) : OldCategory D Sc cut :=
  ⟨v ++ [i] ++ [i] ++ [i]⟩
private def R (v : List Bool) (i : Bool) := oldRepresentable D Sc cut (upper v i)
private def vector (v : List Bool) (i : Bool) : (R v i).obj (upper v i) := by
  let x : (R v i).obj (upper v i) := 𝟙 (upper v i)
  let y : (R v i).obj (upper v i) :=
    oldAppendDotComponent D Sc cut i ⟨v ++ [i] ++ [i]⟩
  exact x + y

/-- Both moving parities, with empty and mixed old contexts. -/
example (i : Bool) := equalCrossComponent_braid D Sc cut i (source [])
example (i : Bool) := equalCrossComponent_braid D Sc cut i (source [false,true])

/-- The literal old representable evaluates the braid on an identity-plus-dot vector. -/
example (i : Bool) := congrArg
  (fun f : End (upper [false,true] i) =>
    (R [false,true] i).map f (vector [false,true] i))
  (equalCrossComponent_braid D Sc cut i (source [false,true]))

/-- It holds on every vector, not merely on the displayed test vector. -/
example (i : Bool) (v : (R [] i).obj (upper [] i)) := congrArg
  (fun f : End (upper [] i) => (R [] i).map f v)
  (equalCrossComponent_braid D Sc cut i (source []))
end OldAppendBraidConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
