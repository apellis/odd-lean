import OddMath.SKM.RouquierDistinctCapMonomials
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCapMonomials
private abbrev D := AsymmetricParameters.datum
private abbrev S := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D S
private def m : Bool → ℕ := fun _ => 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D Sc m Λ cutoff
private def a : Bool → ℤ := -Λ
private theorem square (i j : Bool) : (a + D.α j) + D.α i = (a + D.α i) + D.α j := by abel
private theorem negative_upper (i : Bool) : D.h i ((a + D.α i) + D.α (!i)) < -1 := by
  cases i <;> norm_num [a, Λ, m, D, AsymmetricParameters.datum, Datum.h, Datum.α,
    probeCutoff, probeDotExponent]

/-- Both colours are odd, distinct, and have occupied nonzero probe append vectors. -/
example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)

example (i : Bool) (s q : ℕ) :=
  (T.distinctMixedBraidOuterMate_monomial_cap i (!i)
    (show a + D.α i = a + D.α i from rfl) rfl rfl (square i (!i))
    (lt_trans (negative_upper i) (by omega)) s q 0 (by
      have hc := negative_upper i
      omega)).trans (ite_eq_right (by
        have hc := negative_upper i
        omega))

example (i : Bool) (s q : ℕ) :=
  (T.distinctMixedBraidOuterMate_monomial_cap i (!i)
    (show a + D.α i = a + D.α i from rfl) rfl rfl (square i (!i))
    (lt_trans (negative_upper i) (by omega)) s q
    (-D.h i ((a + D.α i) + D.α (!i)) - 1).toNat (by
      have hc := negative_upper i
      omega)).trans (ite_eq_left rfl)

end NonVacuity.RouquierDistinctCapMonomials
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCapMonomials
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty audit"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
