import OddMath.QuiverHecke.CyclotomicAction.ELVGridLocalInverseFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open BalancedInduction CyclotomicCrossingTensor
namespace GridLocalInverseFamiliesConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private theorem unitSign (i : Bool) : 0 ≤ contentCrossingHeight D cut i ([i] : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem capSign (i : Bool) : contentCrossingHeight D cut i ([i,i,i] : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private def unitData (i : Bool) := gridLocalInverseFromFamily
  (oldContentAppend D Sc cut [] i) (oldContentAppend D Sc cut [i] i)
  (oldContentMatrixCross_supernatural D Sc cut [] i)
  (oldContentAppendDot_supernatural D Sc cut [i] i)
  (contentUnitCount D cut i ([i] : Multiset Bool))
  (fun N => oldContentGridUnitMatrixIso D Sc cut [] i N (unitSign i))
  (fun N => oldContentGridUnitMatrixIso_hom D Sc cut [] i N (unitSign i))
private def capData (i : Bool) := gridLocalInverseToFamily
  (oldContentAppend D Sc cut [i,i] i) (oldContentAppend D Sc cut [i,i,i] i)
  (oldContentMatrixCross_supernatural D Sc cut [i,i] i)
  (oldContentAppendDot_supernatural D Sc cut [i,i] i)
  (contentCapCount D cut i ([i,i,i] : Multiset Bool))
  (fun N => oldContentGridCapMatrixIso D Sc cut [i,i] i N (capSign i))
  (fun N => oldContentGridCapMatrixIso_hom D Sc cut [i,i] i N (capSign i))
/-- Both parities use constructed inverses of the prescribed matrices. -/
example (i : Bool) := (unitData i).total
example (i : Bool) := (unitData i).ff
example (i : Bool) := (unitData i).f'_mem
example (i : Bool) (m : ℕ) := (unitData i).g'_mem m
example (i : Bool) := (capData i).total
example (i : Bool) := (capData i).ff
example (i : Bool) := (capData i).f'_mem
example (i : Bool) (m : ℕ) := (capData i).g'_mem m
example (i : Bool) := (unitData i).fg 0 (by cases i <;> decide)
example (i : Bool) := (unitData i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (capData i).gf 0 (by cases i <;> decide)
example (i : Bool) := (capData i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
end GridLocalInverseFamiliesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVGridLocalInverseFamilies
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
