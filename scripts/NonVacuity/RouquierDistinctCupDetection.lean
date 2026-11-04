import OddMath.SKM.RouquierDistinctCupDetection
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCupDetection
private abbrev D := AsymmetricParameters.datum
private abbrev S := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D S
private def m : Bool → ℕ := fun _ => 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D Sc m Λ cutoff
private theorem rels : RouquierMulticolour T S := probeOldRouquierMulticolour D S m Λ cutoff
private def a (i : Bool) : Bool → ℤ := -Λ + 4 • D.α i
private theorem square (i j : Bool) : (a i + D.α j) + D.α i =
    (a i + D.α i) + D.α j := by abel
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem positive (i : Bool) : 0 ≤ D.h i ((a i + D.α i) + D.α (!i)) := by
  cases i <;> norm_num [a, Λ, m, D, AsymmetricParameters.datum, Datum.h, Datum.α,
    probeCutoff, probeDotExponent]

/-- Both colours are odd, distinct, and have occupied nonzero probe append vectors. -/
example (i : Bool) : probeOldVacuumAppendVector D Sc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide)

example (i : Bool) : IsIso
    (T.distinctCupTarget (i := i) (j := !i) (a := a i) rfl rfl rfl (square i (!i))) :=
  T.distinctCupTarget_isIso rels (distinct i) rfl rfl rfl (square i (!i))

/-- The actual positive-height test family and all finite rows are supplied;
one colour also exercises the zero-height orientation. -/
example (i : Bool) :
    (2 : ℚ) • 𝟙 ((T.F i (show a i + D.α i = a i + D.α i from rfl) ≫
      T.E (!i) (show a i + D.α (!i) = a i + D.α (!i) from rfl)) ≫
      T.E i (square i (!i))) = 𝟙 _ + 𝟙 _ := by
  apply T.distinctCup_hom_ext_of_nonneg rels (distinct i) rfl rfl rfl
    (square i (!i)) rfl (positive i)
  · simp only [Preadditive.add_comp, Category.id_comp, two_smul]
  · intro n hn
    simp only [Preadditive.add_comp, Category.id_comp, two_smul]

end NonVacuity.RouquierDistinctCupDetection
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCupDetection
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty audit"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
