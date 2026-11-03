import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctTargets
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentDistinctTargetsConsumer
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
private def M (j : Bool) := supermoduleParityObj
  ((BalancedInduction.restriction (contentInclusion D Sc cut 8 (δ j))).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨j :: [false,true]⟩)))

/-- Nonempty source content retains the prescribed successor ordering and all certificates. -/
example (i : Bool) := contentDistinctTargetsMate_isIso D Sc cut 8 β i (!i)
  (δ (!i)) (δ i) (γ i (!i)) (hj (!i)) (hj i) (hL i (!i)) (hU i (!i)) (distinct i) (M (!i))
example (i : Bool) := contentDistinctTargetsFunctor_isIso D Sc cut 8 β i (!i)
  (δ (!i)) (δ i) (γ i (!i)) (hj (!i)) (hj i) (hL i (!i)) (hU i (!i)) (distinct i)
example := contentDistinctTargetsFunctor_isIso AsymmetricParameters.datum AsymmetricParameters.scalars cut 8
  β false true (δ true) (δ false) (γ false true) (hj true) (hj false) (hL false true) (hU false true) (by decide)
end ContentDistinctTargetsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctTargets
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
