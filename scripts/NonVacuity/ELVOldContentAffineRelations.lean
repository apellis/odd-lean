import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAffineRelations
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace OldContentAffineRelationsConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def source (v : List Bool) : OldContentCategory D Sc cut v :=
  ⟨⟨v⟩, List.Perm.refl _⟩
private def upper (v : List Bool) (i : Bool) : OldCategory D Sc cut := ⟨v ++ [i] ++ [i]⟩
private def R (v : List Bool) (i : Bool) := oldRepresentable D Sc cut (upper v i)
private def vector (v : List Bool) (i : Bool) : (R v i).obj (upper v i) := by
  let x : (R v i).obj (upper v i) := 𝟙 (upper v i)
  let y : (R v i).obj (upper v i) := oldAppendDotComponent D Sc cut i ⟨v ++ [i]⟩
  exact x + y
/-- Both moving parities satisfy all three literal quotient relations, including the empty old content. -/
example (i : Bool) := oldContentEqualCross_square D Sc cut [] i (source [])
example (i : Bool) := oldContentEqualCross_slideLeft D Sc cut [] i (source [])
example (i : Bool) := oldContentEqualCross_slideRight D Sc cut [] i (source [])
example (i : Bool) := oldContentEqualCross_square D Sc cut [false,true] i (source [false,true])
example (i : Bool) := oldContentEqualCross_slideLeft D Sc cut [false,true] i (source [false,true])
example (i : Bool) := oldContentEqualCross_slideRight D Sc cut [false,true] i (source [false,true])
/-- The actual old representable evaluates the square and both slides on an identity-plus-dot vector. -/
example (i : Bool) := congrArg
  (fun f : End (upper [false,true] i) => (R [false,true] i).map f (vector [false,true] i))
  (oldContentEqualCross_square D Sc cut [false,true] i (source [false,true]))
example (i : Bool) := congrArg
  (fun f : End (upper [false,true] i) => (R [false,true] i).map f (vector [false,true] i))
  (oldContentEqualCross_slideLeft D Sc cut [false,true] i (source [false,true]))
example (i : Bool) := congrArg
  (fun f : End (upper [false,true] i) => (R [false,true] i).map f (vector [false,true] i))
  (oldContentEqualCross_slideRight D Sc cut [false,true] i (source [false,true]))
end OldContentAffineRelationsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAffineRelations
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
