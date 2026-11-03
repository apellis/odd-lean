import OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctSlides
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace OldDistinctSlidesConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 6
private def source (v : List Bool) : OldCategory D Sc cut := ⟨v⟩
private def lower (v : List Bool) (i : Bool) : OldCategory D Sc cut := ⟨v ++ [!i] ++ [i]⟩
private def upper (v : List Bool) (i : Bool) : OldCategory D Sc cut := ⟨v ++ [i] ++ [!i]⟩
private def R (v : List Bool) (i : Bool) := oldRepresentable D Sc cut (lower v i)
private theorem ne (i : Bool) : i ≠ !i := by cases i <;> decide

example (i : Bool) := Distinct.crossComponent_slide_first D Sc cut (ne i) (source [])
example (i : Bool) := Distinct.crossComponent_slide_last D Sc cut (ne i) (source [false,true])

/-- Both equations act on every vector of the occupied representable component. -/
example (i : Bool) (v : (R [false,true] i).obj (lower [false,true] i)) := congrArg
  (fun f : lower [false,true] i ⟶ upper [false,true] i => (R [false,true] i).map f v)
  (Distinct.crossComponent_slide_first D Sc cut (ne i) (source [false,true]))
example (i : Bool) := congrArg
  (fun f : lower [false,true] i ⟶ upper [false,true] i =>
    (R [false,true] i).map f (𝟙 (lower [false,true] i)))
  (Distinct.crossComponent_slide_last D Sc cut (ne i) (source [false,true]))

private abbrev Do := CyclotomicAction.AsymmetricParameters.datum
private abbrev So := CyclotomicAction.AsymmetricParameters.scalars
/-- The two-odd crossing retains its nontrivial negative slide sign. -/
example (i : Bool) := Distinct.crossComponent_slide_first Do So cut (ne i)
  (⟨[false,true]⟩ : OldCategory Do So cut)
example (i : Bool) := Distinct.crossComponent_slide_last Do So cut (ne i)
  (⟨[false,true]⟩ : OldCategory Do So cut)
example : sign ℚ (Do.parity false * Do.parity true) = -1 := by
  change sign ℚ (1 * 1) = -1
  rw [one_mul, sign_one]
end OldDistinctSlidesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctSlides
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
