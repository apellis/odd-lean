import OddMath.SKM.RouquierDistinctCupPitchfork
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCupPitchfork
private abbrev D := AsymmetricParameters.datum
private abbrev S := AsymmetricParameters.transportedScalars
private abbrev Sc := parameterTwist D S
private def m : Bool → ℕ := fun _ => 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D Sc m Λ cutoff
private theorem rels : RouquierMulticolour T S := probeOldRouquierMulticolour D S m Λ cutoff
private def a (i : Bool) : Bool → ℤ := -Λ + 5 • D.α i
private theorem square (i j : Bool) : (a i + D.α j) + D.α i =
    (a i + D.α i) + D.α j := by abel
private theorem upper_square (i j : Bool) : ((a i + D.α i) + D.α i) + D.α j =
    ((a i + D.α i) + D.α j) + D.α i := by abel
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem strict (i : Bool) : D.d i (!i) < D.h i (a i + D.α i) := by
  cases i <;> norm_num [a, Λ, m, D, AsymmetricParameters.datum, Datum.h, Datum.d,
    Datum.α, probeCutoff, probeDotExponent]

example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)

example (i : Bool) := T.distinctCupLeft_eq_of_gt rels (distinct i)
  (show a i + D.α i = a i + D.α i from rfl)
  (show a i + D.α (!i) = a i + D.α (!i) from rfl)
  rfl (square i (!i)) rfl rfl (upper_square i (!i)) (strict i)

example : (S.t true false : ℚ) = -1 := rfl
example : (S.t false true : ℚ) = 1 := rfl
end NonVacuity.RouquierDistinctCupPitchfork

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCupPitchfork
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty audit"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
