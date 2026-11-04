import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightWindowInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCentreBlocks
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVWeightWindowInverseCoordinates
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def Λ : Bool → ℤ := fun _ => 4
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩
private theorem cutoff (i : Bool) : (cut i : ℤ) = D.h i Λ := rfl
private def M (v : List Bool) (i : Bool) : ELVWeightProduct D Sc cut 8 Λ (w v + D.α i) := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v ++ [i]⟩)))
private theorem negative (i : Bool) : D.h i (w [] + D.α i) ≤ 0 := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem positive (i : Bool) : 0 ≤ D.h i (w [i,i] + D.α i) := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
example (i : Bool) (j : Fin (D.h i (w [i,i] + D.α i)).toNat) :=
  elvChosenCapWindow_coordinates D Sc cut 8 Λ cutoff i rfl rfl
    (M [i,i] i) (base [i,i]) (positive i) j.val j.isLt
example (i : Bool) (j : Fin (-D.h i (w [] + D.α i)).toNat) :=
  elvChosenUnitWindow_coordinates D Sc cut 8 Λ cutoff i rfl rfl
    (M [] i) (base []) (negative i) j.val j.isLt
example (i : Bool) : 0 < (D.h i (w [i,i] + D.α i)).toNat := by
  cases i <;> decide
example (i : Bool) : 0 < (-D.h i (w [] + D.α i)).toNat := by
  cases i <;> decide
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end NonVacuity.ELVWeightWindowInverseCoordinates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightWindowInverseCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
