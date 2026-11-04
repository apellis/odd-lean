import OddMath.SKM.RouquierDistinctCapColumnReduction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Both ordered pairs in the constructed two-odd probe family satisfy
the exact source-chart column reduction for every dot power and principal-word identity. All hypotheses are proved. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCapColumnReduction
private abbrev D := AsymmetricParameters.datum
private abbrev S := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D S
private def m : Bool → ℕ := fun _ => 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D Sc m Λ cutoff
private theorem rels : RouquierMulticolour T S := probeOldRouquierMulticolour D S m Λ cutoff
private def a : Bool → ℤ := -Λ
private theorem square (i j : Bool) :
    (a + D.α j) + D.α i = (a + D.α i) + D.α j := by abel
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide

private theorem upper (i j : Bool) :
    ((a + D.α i) + D.α i) + D.α j = ((a + D.α i) + D.α j) + D.α i := by abel

example (i : Bool) (n : ℕ) := T.distinctCapLeft_column_reduce rels (distinct i)
  (show a + D.α i = a + D.α i from rfl)
  rfl rfl (upper i (!i)) rfl (square i (!i)) n

example (i : Bool) := T.distinctCapLeft_principal_word
  (show a + D.α i = a + D.α i from rfl)
  rfl rfl (upper i (!i)) rfl (square i (!i))

example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)

end NonVacuity.RouquierDistinctCapColumnReduction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCapColumnReduction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
