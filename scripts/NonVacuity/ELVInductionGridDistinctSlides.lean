import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace InductionGridDistinctSlidesConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 6
private abbrev J (ν : List Bool) (j : Bool) := oldContentAppend D Sc cut ν j
private abbrev T (ν : List Bool) (i j : Bool) := oldContentDistinctUpperAppend D Sc cut ν i j
private def R (ν : List Bool) := (restriction (oldContentInclusion D Sc cut ν)).obj
  (oldRepresentable D Sc cut (⟨ν⟩ : OldCategory D Sc cut))
private def upperDot (ν : List Bool) (i j : Bool)
    (s : OldContentCategory D Sc cut (i :: ν)) : (T ν i j).obj s ⟶ (T ν i j).obj s :=
  oldAppendDotComponent D Sc cut j s.obj
private theorem upperDot_supernatural (ν : List Bool) (i j : Bool) :
    IsSupernatural ℚ (D.parity j) (upperDot ν i j) where
  mem s := (oldAppendDot_supernatural D Sc cut j).mem s.obj
  naturality hf := (oldAppendDot_supernatural D Sc cut j).naturality hf
private theorem ne (i : Bool) : i ≠ !i := by cases i <;> decide

/-- Four changing content categories retain the common upper target. -/
example (i : Bool) := rectangularCrossComponent_slide_inner_outer
  (J [false,true] (!i)) (J [false,true] i) (J ((!i) :: [false,true]) i)
  (T [false,true] i (!i)) (oldContentDistinctCross_supernatural D Sc cut [false,true] i (!i))
  (oldContentAppendDot_supernatural D Sc cut [false,true] (!i))
  (upperDot_supernatural [false,true] i (!i))
  (sign ℚ (D.parity (!i) * D.parity i))
  (fun s => Distinct.crossComponent_slide_first D Sc cut (ne i) s.obj) (R [false,true])
example (i : Bool) := rectangularCrossComponent_slide_outer_inner
  (J [] (!i)) (J [] i) (J [!i] i) (T [] i (!i))
  (oldContentDistinctCross_supernatural D Sc cut [] i (!i))
  (oldContentAppendDot_supernatural D Sc cut [!i] i)
  (oldContentAppendDot_supernatural D Sc cut [] i)
  (sign ℚ (D.parity (!i) * D.parity i))
  (fun s => Distinct.crossComponent_slide_last D Sc cut (ne i) s.obj)
  (supermoduleParityObj (R []))
end InductionGridDistinctSlidesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridDistinctSlides
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
