import OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedCapInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor
namespace ContentWeightedCapInverseConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def input (v : List Bool) := supermoduleParityObj
  (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
    ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩))
private theorem capSign (i : Bool) :
    contentCrossingHeight D cut i ([i,i,i] : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem zeroSign (i : Bool) :
    contentCrossingHeight D cut i ([i,i] : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private def capData (i : Bool) := weightedContentLocalInverseTo D Sc cut 8 i
  (input [i,i,i]) [i,i,i] (capSign i)
private def zeroData (i : Bool) := weightedContentLocalInverseTo D Sc cut 8 i
  (input [i,i]) [i,i] (zeroSign i)
/-- Both parities use the constructed inverse of the exact given weighted cap matrix. -/
example (i : Bool) := (capData i).total
example (i : Bool) := (capData i).ff
example (i : Bool) := (capData i).f'_mem
example (i : Bool) (n : ℕ) := (capData i).g'_mem n
example (i : Bool) := (capData i).fg 0 (by cases i <;> decide)
example (i : Bool) := (capData i).gf 0 (by cases i <;> decide)
example (i : Bool) := (capData i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
/-- The zero-height finite window is included in the same construction. -/
example (i : Bool) := (zeroData i).total
example (i : Bool) := (zeroData i).ff
example (i : Bool) := (zeroData i).f'_mem
end ContentWeightedCapInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedCapInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
