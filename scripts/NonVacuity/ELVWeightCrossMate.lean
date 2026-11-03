import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightCrossMateConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem h₁ (i : Bool) : (0 : Bool → ℤ) + D.α (!i) = D.α (!i) := zero_add _
private theorem h₂ (i : Bool) : D.α (!i) + D.α i = D.α (!i) + D.α i := rfl
private theorem h₃ (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private theorem h₄ (i : Bool) : D.α i + D.α (!i) = D.α (!i) + D.α i := add_comm _ _
private def rawFamily (i : Bool) : ELVWeightProduct D Sc cut 8 0 (D.α i) := fun δ =>
  (BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[i]⟩))
private def shiftedFamily (i : Bool) : ELVWeightProduct D Sc cut 8 0 (D.α i) :=
  fun δ => supermoduleParityObj (rawFamily i δ)
private def inputMap (i : Bool) : shiftedFamily i ⟶ rawFamily i :=
  fun δ => (supermoduleParityIso (rawFamily i δ)).hom
private theorem inputMap_mem (i : Bool) : inputMap i ∈ parity (R := ℚ) _ _ 1 :=
  fun δ => supermoduleParityIso_hom_mem (rawFamily i δ)

example (i : Bool) := elvActionCrossMate_eq D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i)
example (i : Bool) := elvActionCrossMate_isIso D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i)
example (i : Bool) := elvActionCrossMate_isIso D Sc (fun _ => 0) 0 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i)

section WholeMaps
variable (i : Bool)
local notation "σ" => SKM.crossMate (elvActionAdjunction D Sc cut 8 i 0 (h₃ i))
  (elvActionAdjunction D Sc cut 8 i 0 (h₂ i))
  (elvActionCross D Sc cut 8 i (!i) 0 (h₁ i) (h₂ i) (h₃ i) (h₄ i))
local notation "hi" => elvActionCrossMate_isIso D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i)
example := let : IsIso σ := hi; (asIso σ).hom_inv_id
example := let : IsIso σ := hi; (asIso σ).inv_hom_id
/-- Evaluate the presentation mate on the actual shifted representable input. -/
example (p : ZMod 2) := congrArg (fun f => f.app p (shiftedFamily i))
  (elvActionCrossMate_eq D Sc cut 8 i (!i) 0 (h₁ i) (h₂ i) (h₃ i) (h₄ i))
/-- The constructed inverse is natural against the odd parity isomorphism. -/
example := let : IsIso σ := hi
  (inv σ).naturality 1 (inputMap i) (inputMap_mem i)
end WholeMaps

/-- Distinct odd colours test the odd sideways crossing, in both orientations. -/
example (i : Bool) := elvActionCrossMate_isIso AsymmetricParameters.datum
  AsymmetricParameters.scalars cut 8 i (!i) 0
  (zero_add _) (rfl : AsymmetricParameters.datum.α (!i) + AsymmetricParameters.datum.α i = _)
  (zero_add _) (add_comm _ _) (distinct i)
end WeightCrossMateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossMate
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
