import OddMath.SKM.RouquierDistinctCapDetection
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCapDetection
private abbrev D := AsymmetricParameters.datum
private abbrev S := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D S
private def m : Bool → ℕ := fun _ => 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D Sc m Λ cutoff
private theorem rels : RouquierMulticolour T S := probeOldRouquierMulticolour D S m Λ cutoff
private def a : Bool → ℤ := -Λ
private theorem before (i : Bool) : (a - D.α i) + D.α i = a := sub_add_cancel _ _
private theorem square (i j : Bool) : (a + D.α j) + D.α i = (a + D.α i) + D.α j := by abel
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem negative (i : Bool) : D.h i a ≤ 0 := by
  cases i <;> norm_num [a, Λ, m, D, AsymmetricParameters.datum, Datum.h,
    probeCutoff, probeDotExponent]

/-- Both colours are odd, distinct, and have occupied nonzero probe append vectors. -/
example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)

example (i : Bool) : IsIso
    (T.distinctCapSource (i := i) (j := !i) (a := a) rfl rfl rfl (square i (!i))) :=
  T.distinctCapSource_isIso rels (distinct i) rfl rfl rfl (square i (!i))

/-- All principal and finite-column tests are proved for these concrete
maps in the actual two-odd factor; no matrix or pitchfork test is assumed. -/
example (i : Bool) :
    (2 : ℚ) • 𝟙 ((T.E i (show a + D.α i = a + D.α i from rfl) ≫
      T.E (!i) (show (a + D.α i) + D.α (!i) = (a + D.α i) + D.α (!i) from rfl)) ≫
      T.F i (square i (!i))) =
    𝟙 _ + 𝟙 _ := by
  apply T.distinctCap_hom_ext_of_nonpos rels (distinct i) (before i) rfl rfl rfl
    (square i (!i)) (negative i)
  · simp only [Preadditive.comp_add, Category.comp_id, two_smul]
  · intro n hn
    simp only [Preadditive.comp_add, Category.comp_id, two_smul]

end NonVacuity.RouquierDistinctCapDetection
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCapDetection
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty audit"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
