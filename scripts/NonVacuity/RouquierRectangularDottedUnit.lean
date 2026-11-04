import OddMath.SKM.RouquierRectangularDottedUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Both ordered pairs in the constructed two-odd probe family satisfy
the dotted unit pitchfork with an odd dot and odd crossing. All hypotheses are proved. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierRectangularDottedUnit
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

example (i : Bool) := crossMate_pitchfork_unit_dotted
  (T.adj i (show a + D.α i = a + D.α i from rfl))
  (T.adj i (square i (!i))) _ _
  (T.cross i (!i) rfl (square i (!i)) rfl rfl)
  (T.dot i rfl) (T.dot i (square i (!i)))
  (T.dot_mem i rfl) (T.cross_mem i (!i) rfl (square i (!i)) rfl rfl)
  (by
    have hs := rels.slideLeft i (!i) (distinct i)
      (show a + D.α (!i) = a + D.α (!i) from rfl) (square i (!i)) rfl rfl
    cases i <;> simpa [D, AsymmetricParameters.datum, koszulSign, zsign] using hs)

example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)

end NonVacuity.RouquierRectangularDottedUnit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierRectangularDottedUnit
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
