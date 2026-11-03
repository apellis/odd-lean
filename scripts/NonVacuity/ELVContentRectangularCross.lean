import OddMath.QuiverHecke.CyclotomicAction.ELVContentRectangularCross
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentRectangularCrossConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev β : Multiset Bool := [false,true]
private abbrev δ (i : Bool) : Multiset Bool := ([i] : Multiset Bool) + β
private abbrev γ (i j : Bool) : Multiset Bool := ([j] : Multiset Bool) + (([i] : Multiset Bool) + β)
private theorem hj (j : Bool) : β + ([j] : Multiset Bool) = δ j := by
  change β + {j} = {j} + β
  exact add_comm _ _
private theorem hL (i j : Bool) : δ j + ([i] : Multiset Bool) = γ i j := by
  change ({j} + β) + {i} = {j} + ({i} + β)
  ac_rfl
private theorem hU (i j : Bool) : δ i + ([j] : Multiset Bool) = γ i j := by
  change ({i} + β) + {j} = {j} + ({i} + β)
  ac_rfl
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem hji (i j : Bool) : β + ([j,i] : Multiset Bool) = γ i j := by
  change β + ({j} + {i}) = {j} + ({i} + β)
  ac_rfl
private theorem hij (i j : Bool) : β + ([i,j] : Multiset Bool) = γ i j := by
  change β + ({i} + {j}) = {j} + ({i} + β)
  ac_rfl
private def P := supermoduleParityObj
  ((BalancedInduction.restriction (contentInclusion D Sc cut 8 β)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[false,true]⟩)))
private def word : ContentCategory D Sc cut 8 β :=
  ⟨(oldTruncateFunctor D Sc cut 8).obj ⟨[false,true]⟩, by rfl⟩

/-- Both mixed orders preserve the exact word comparison and stored contents. -/
example (i : Bool) := contentDistinctTargetsCross_coefficient D Sc cut 8 β i (!i)
  (δ (!i)) (δ i) (γ i (!i)) (hj (!i)) (hj i) (hL i (!i)) (hU i (!i))
  (hji i (!i)) (hij i (!i)) (distinct i) word
example (i : Bool) := contentDistinctTargetsCross_comparison D Sc cut 8 β i (!i)
  (δ (!i)) (δ i) (γ i (!i)) (hj (!i)) (hj i) (hL i (!i)) (hU i (!i))
  (hji i (!i)) (hij i (!i)) (distinct i) P
example := contentCrossAffine_reverse_mem AsymmetricParameters.datum AsymmetricParameters.scalars false true
end ContentRectangularCrossConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentRectangularCross
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
