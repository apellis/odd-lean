import OddMath.QuiverHecke.CyclotomicAction.ELVWeightRectangularCross
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightRectangularCrossConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private def family (x : Bool → ℤ) (v : List Bool) : ELVWeightProduct D Sc cut 8 0 x := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩)))

private def lowerBlock : WeightBlocks D 0 (0 : Bool → ℤ) := ⟨0, by simp⟩
private theorem h₁ (i : Bool) : (0 : Bool → ℤ) + D.α (!i) = D.α (!i) := zero_add _
private theorem h₂ (i : Bool) : D.α (!i) + D.α i = D.α (!i) + D.α i := rfl
private theorem h₃ (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private theorem h₄ (i : Bool) : D.α i + D.α (!i) = D.α (!i) + D.α i := add_comm _ _

private abbrev upper (i : Bool) := blockSucc₂ D i (!i) 0 (h₁ i) (h₂ i) lowerBlock

/-- The selected pair comparison and crossing agree on both supported mixed orders. -/
example (i : Bool) := elvWeightPairUpper_content_eq D i (!i) 0 (h₁ i) (h₂ i)
  lowerBlock (upper i) rfl
example (i : Bool) := elvEFunctor_comp₂_rectangular_eq D Sc cut 8 i (!i) 0 (h₁ i) (h₂ i)
  lowerBlock (upper i) rfl
example (i : Bool) := elvWeightPairComparison_rectangular_eq D Sc cut 8 i (!i) 0 (h₁ i) (h₂ i)
  lowerBlock (upper i) rfl
example (i : Bool) := elvWeightCrossVia_rectangular D Sc cut 8 i (!i) 0 (h₁ i) (h₂ i)
  lowerBlock (upper i) rfl (h₃ i) (h₄ i) (distinct i) (family 0 [])

private def oddLower : WeightBlocks AsymmetricParameters.datum 0 (0 : Bool → ℤ) := ⟨0, by simp⟩
private def oddFamily : ELVWeightProduct AsymmetricParameters.datum AsymmetricParameters.scalars cut 8
    0 (0 : Bool → ℤ) := fun δ => supermoduleParityObj
  ((BalancedInduction.restriction
    (contentInclusion AsymmetricParameters.datum AsymmetricParameters.scalars cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable AsymmetricParameters.datum AsymmetricParameters.scalars cut 8
      ((oldTruncateFunctor AsymmetricParameters.datum AsymmetricParameters.scalars cut 8).obj ⟨[]⟩)))
/-- Distinct odd colours retain the odd selected crossing, including the parity-shifted input. -/
example := elvWeightCrossVia_rectangular AsymmetricParameters.datum AsymmetricParameters.scalars cut 8
  false true 0 (zero_add _) (rfl : AsymmetricParameters.datum.α true + AsymmetricParameters.datum.α false = _)
  oddLower (blockSucc₂ AsymmetricParameters.datum false true 0 (zero_add _) rfl oddLower) rfl
  (zero_add _) (add_comm _ _) (by decide) oddFamily
end WeightRectangularCrossConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightRectangularCross
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
