import OddMath.SKM.RouquierDistinctCapNonpositive
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Both ordered pairs in the constructed two-odd probe family satisfy
the entire raw cap pitchfork at negative and zero central height.
All multicolour, edge and height hypotheses are proved here. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCapNonpositive
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
private theorem upper (i j : Bool) :
    ((a + D.α i) + D.α i) + D.α j = ((a + D.α i) + D.α j) + D.α i := by abel
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide

private theorem negative (i : Bool) : D.h i (a + D.α i) < 0 := by
  cases i <;> norm_num [a, Λ, m, D, AsymmetricParameters.datum, Datum.h, Datum.α,
    probeCutoff, probeDotExponent]

example (i : Bool) := T.distinctCap_of_nonpos rels (distinct i)
  (show a + D.α i = a + D.α i from rfl)
  rfl rfl (upper i (!i)) rfl (square i (!i)) (le_of_lt (negative i))

example (i : Bool) := T.distinctCap_of_nonpos rels (distinct i)
  (show -D.α i + D.α i = 0 from neg_add_cancel _)
  (show 0 + D.α i = D.α i from zero_add _)
  (show 0 + D.α (!i) = D.α (!i) from zero_add _)
  rfl (add_comm (D.α (!i)) (D.α i)) (sub_add_cancel (D.α (!i)) (D.α i))
  (by simp [Datum.h])

example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)

end NonVacuity.RouquierDistinctCapNonpositive

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCapNonpositive
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
