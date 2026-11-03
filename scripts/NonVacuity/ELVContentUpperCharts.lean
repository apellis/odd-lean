import OddMath.QuiverHecke.CyclotomicAction.ELVContentUpperCharts
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace ContentUpperChartsConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def cut : Bool → ℕ := fun _ => 8
private abbrev γ (i : Bool) : List Bool := [!i]
private abbrev t (i : Bool) : OldContentCategory D Sc cut (γ i) :=
  oldContentObject D Sc cut (γ i) ⟨γ i,List.Perm.refl _⟩
private def N (i : Bool) := (restriction (oldContentInclusion D Sc cut (γ i))).obj
  (oldRepresentable D Sc cut (t i).obj)
private def G (i : Bool) := induced (oldContentInclusion D Sc cut (γ i)) (N i)
private abbrev J (i : Bool) := append D Sc cut i
private theorem missing (i : Bool) : i ∉ γ i := by cases i <;> decide

/-- Full following F/E and value charts at missing-colour outputs. -/
example (i : Bool) := oldContentFEChart D Sc cut (γ i) i (N i) (t i)
example (i : Bool) := oldContentValueChart D Sc cut (γ i) (N i) (t i)
example (i : Bool) (z : Obj (oldContentAppend D Sc cut (γ i) i) (N i).toFunctor
    ((oldContentAppend D Sc cut (γ i) i).obj (t i))) :=
  oldContentFEChart_apply D Sc cut (γ i) i (N i) (t i) z
example (i : Bool) (b : (N i).obj (t i)) :=
  oldContentValueChart_apply D Sc cut (γ i) (N i) (t i) b
example (i : Bool) (n : ℕ) (b : (N i).obj (t i)) :=
  oldContentFEChart_unitDot D Sc cut (γ i) i (N i) (t i) n b

private abbrev vacuum : OldContentCategory D Sc cut [] :=
  oldContentObject D Sc cut [] ⟨[],List.Perm.refl _⟩
private def N0 := (restriction (oldContentInclusion D Sc cut [])).obj
  (oldRepresentable D Sc cut vacuum.obj)
private theorem missing0 (i : Bool) : i ∉ ([] : List Bool) := by simp

/-- Genuine EMPTY OUTPUT retains every unit/dot column under these charts. -/
example (i : Bool) := oldContentFEChart D Sc cut [] i N0 vacuum
example := oldContentValueChart D Sc cut [] N0 vacuum
example (i : Bool) (n : ℕ) (b : N0.obj vacuum) :=
  oldContentFEChart_unitDot D Sc cut [] i N0 vacuum n b

end ContentUpperChartsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentUpperCharts
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
