import OddMath.SKM.RouquierDistinctCanonicalPositive
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Both ordered pairs in the constructed nonzero two-odd probe family
satisfy canonical distinct left-mate invertibility in the strict cup range.
The positive weights are actual root-content weights and all hypotheses are proved. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCanonicalPositive
private abbrev D := AsymmetricParameters.datum
private abbrev S := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D S
private def m : Bool → ℕ := fun _ => 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D Sc m Λ cutoff
private theorem rels : RouquierMulticolour T S := probeOldRouquierMulticolour D S m Λ cutoff
private def a : Bool → ℤ := -Λ
private def pos (i : Bool) : Bool → ℤ := a + 5 • D.α i
private theorem square (i : Bool) :
    (pos i + D.α (!i)) + D.α i = (pos i + D.α i) + D.α (!i) := by abel
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem height (i : Bool) : D.d i (!i) < D.h i (pos i + D.α i) := by
  cases i <;> norm_num [pos, a, Λ, m, D, AsymmetricParameters.datum, Datum.h,
    Datum.α, Datum.d, probeCutoff, probeDotExponent]

example (i : Bool) := T.leftCrossMate_isIso_of_cupRange rels (distinct i)
  (show pos i + D.α i = pos i + D.α i from rfl)
  rfl rfl (square i) (height i)

example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)

end NonVacuity.RouquierDistinctCanonicalPositive

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCanonicalPositive
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
