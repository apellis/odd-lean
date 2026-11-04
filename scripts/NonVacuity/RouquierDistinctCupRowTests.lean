import OddMath.SKM.RouquierDistinctCupRowTests
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCupRowTests
private abbrev D := AsymmetricParameters.datum
private abbrev S := AsymmetricParameters.transportedScalars
private def m (_ : Bool) : ℕ := 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D (parameterTwist D S) m Λ cutoff
private theorem M : RouquierMulticolour T S := probeOldRouquierMulticolour D S m Λ cutoff
private def b (i : Bool) : Bool → ℤ := -Λ + 6 • D.α i
private def a (i : Bool) : Bool → ℤ := b i - D.α i
private theorem ne (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem before (i : Bool) : a i + D.α i = b i := sub_add_cancel _ _
private theorem square (i : Bool) : (a i + D.α (!i)) + D.α i = b i + D.α (!i) := by
  rw [a]
  abel
private theorem height (i : Bool) : D.h i (b i) = 6 := by
  cases i <;> norm_num [b, Λ, m, D, Datum.h, Datum.α, AsymmetricParameters.datum,
    probeCutoff, probeDotExponent]
private theorem upperHeight (i : Bool) : D.h i (b i + D.α (!i)) = if i then 2 else 4 := by
  cases i <;> norm_num [b, Λ, m, D, Datum.h, Datum.α, AsymmetricParameters.datum,
    probeCutoff, probeDotExponent]
private theorem strict (i : Bool) : D.d i (!i) < D.h i (b i) := by
  rw [height]
  cases i <;> decide
private theorem upperPositive (i : Bool) : 0 < D.h i (b i + D.α (!i)) := by
  rw [upperHeight]
  cases i <;> decide

/-- All dotted-cap transports and all actual finite rows of the two
asymmetric odd-colour orders, with their distinct leading units. -/
example (i : Bool) (n : ℕ) := T.distinctCrossMate_dottedCap M i (!i) (ne i)
  (show a i + D.α (!i) = a i + D.α (!i) from rfl) (square i) (before i) rfl n
example (i : Bool) (n : ℕ) := T.distinctCupLeft_row_reduce M (ne i)
  (before i) rfl rfl (square i) rfl rfl n
example (i : Bool) (n : Fin ((D.h i (b i + D.α (!i))).toNat)) :=
  T.distinctCupLeft_row_of_gt M (ne i) (before i) rfl rfl (square i) rfl rfl
    (strict i) n.val n.isLt
example (i : Bool) (n : Fin ((D.h i (b i + D.α (!i))).toNat)) :=
  T.distinctCupRight_row_of_pos M (ne i) (before i) rfl rfl (square i) rfl
    (upperPositive i) n.val n.isLt
example : (S.t true false : ℚ) = -1 := rfl
example : (S.t false true : ℚ) = 1 := rfl
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D S) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D S) m i (by cases i <;> decide)
end NonVacuity.RouquierDistinctCupRowTests
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCupRowTests
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"
