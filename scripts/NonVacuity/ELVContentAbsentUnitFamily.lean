import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentUnitFamily
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open BalancedInduction
namespace ContentAbsentUnitFamilyConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def emptyInverse (i : Bool) := Classical.choice
  (contentAbsentUnitFamily_nonempty D Sc cut 8 0 i (by simp))
private def otherInverse (i : Bool) := Classical.choice
  (contentAbsentUnitFamily_nonempty D Sc cut 8 [!i] i (by cases i <;> decide))
private def M : ContentModules D Sc cut 8 0 :=
  (restriction (contentInclusion D Sc cut 8 0)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[]⟩))
private def oddInput : supermoduleParityObj M ⟶ M := (supermoduleParityIso M).hom
private theorem oddInput_mem : oddInput ∈ parity (R := ℚ) _ _ 1 := supermoduleParityIso_hom_mem M
/-- Both moving parities retain the given whole unit families and all inverse identities. -/
example (i : Bool) := (emptyInverse i).total
example (i : Bool) := (emptyInverse i).ff
example (i : Bool) := (emptyInverse i).f'_mem
example (i : Bool) (n : ℕ) := (emptyInverse i).g'_mem n
example (i : Bool) := (otherInverse i).total
example (i : Bool) := (otherInverse i).ff
example (i : Bool) := (otherInverse i).f'_mem
example (i : Bool) (n : ℕ) := (otherInverse i).g'_mem n
/-- The constructed inverse rows are natural against a concrete odd input-module map. -/
example (i : Bool) := ((emptyInverse i).f').naturality (D.parity i) oddInput oddInput_mem
example (i : Bool) := ((emptyInverse i).g' 1).naturality (1 • D.parity i) oddInput oddInput_mem
example (i : Bool) := ((emptyInverse i).g' 7).naturality (7 • D.parity i) oddInput oddInput_mem
example (i : Bool) := (emptyInverse i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
/-- The zero-count whole-family boundary is included without a nonzero-object premise. -/
example (i : Bool) := contentAbsentUnitFamily_nonempty D Sc (fun _ => 0) 0 0 i (by simp)
end ContentAbsentUnitFamilyConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentUnitFamily
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
