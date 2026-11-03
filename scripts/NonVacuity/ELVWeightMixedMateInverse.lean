import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMateInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightMixedMateInverseConsumer
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

/-- The given positive mate is inverted on the actual supported blocks and whole weight products. -/
example (i : Bool) := elvWeightMixedMate_app_block D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) 1 (family (D.α (!i)) [!i])
  (blockSucc D 0 i (h₃ i) lowerBlock)
example (i : Bool) := elvWeightMixedMate_comparison D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) lowerBlock (distinct i) (family (D.α (!i)) [!i])
example (i : Bool) := elvWeightMixedMate_supported_isIso D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) lowerBlock (distinct i) (family (D.α (!i)) [!i])
example (i : Bool) := elvWeightMixedMate_coordinate_isIso D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i) (family (D.α (!i)) [!i])
  (blockSucc D 0 i (h₃ i) lowerBlock)
example (i : Bool) := elvWeightMixedMate_component_isIso D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i) (family (D.α (!i)) [!i])
example (i : Bool) := elvWeightMixedMate_isIso D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i)
example (i : Bool) := elvWeightMixedMate_inverse_mem D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i)
/-- Empty truncation is included without a nonzero-object premise. -/
example (i : Bool) := elvWeightMixedMate_isIso D Sc (fun _ => 0) 0 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i)

section WholeMaps
variable (i : Bool)
local notation "φ" => elvWeightMixedMate D Sc cut 8 i (!i) 0 (h₁ i) (h₂ i) (h₃ i) (h₄ i)
local notation "hi" => elvWeightMixedMate_isIso D Sc cut 8 i (!i) 0 (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i)
example := let : IsIso φ := hi; (asIso φ).hom_inv_id
example := let : IsIso φ := hi; (asIso φ).inv_hom_id
private def rawFamily (x : Bool → ℤ) (v : List Bool) : ELVWeightProduct D Sc cut 8 0 x := fun δ =>
  (BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩))
private def oddMap (x : Bool → ℤ) (v : List Bool) : family x v ⟶ rawFamily x v := fun δ =>
  (supermoduleParityIso (rawFamily x v δ)).hom
private theorem oddMap_mem (x : Bool → ℤ) (v : List Bool) :
    oddMap x v ∈ parity (R := ℚ) _ _ 1 := fun δ => supermoduleParityIso_hom_mem (rawFamily x v δ)
/-- The inverse is natural against a nonzero-degree input-module map. -/
example := let : IsIso φ := hi
  (inv φ).naturality (D.parity i * D.parity (!i)) (oddMap (D.α (!i)) [!i])
    (oddMap_mem (D.α (!i)) [!i])
end WholeMaps

/-- Two distinct odd colours retain the odd given forward and inverse. -/
example := elvWeightMixedMate_isIso AsymmetricParameters.datum AsymmetricParameters.scalars cut 8 false true 0
  (zero_add _) (rfl : AsymmetricParameters.datum.α true + AsymmetricParameters.datum.α false = _)
  (zero_add _) (add_comm _ _) (by decide)
example := elvWeightMixedMate_inverse_mem AsymmetricParameters.datum AsymmetricParameters.scalars cut 8 false true 0
  (zero_add _) (rfl : AsymmetricParameters.datum.α true + AsymmetricParameters.datum.α false = _)
  (zero_add _) (add_comm _ _) (by decide)
section OddMaps
private theorem oh₁ : (0 : Bool → ℤ) + AsymmetricParameters.datum.α true =
    AsymmetricParameters.datum.α true := zero_add _
private theorem oh₂ : AsymmetricParameters.datum.α true + AsymmetricParameters.datum.α false =
    AsymmetricParameters.datum.α true + AsymmetricParameters.datum.α false := rfl
private theorem oh₃ : (0 : Bool → ℤ) + AsymmetricParameters.datum.α false =
    AsymmetricParameters.datum.α false := zero_add _
private theorem oh₄ : AsymmetricParameters.datum.α false + AsymmetricParameters.datum.α true =
    AsymmetricParameters.datum.α true + AsymmetricParameters.datum.α false := add_comm _ _
private def oddRawInput : ELVWeightProduct AsymmetricParameters.datum AsymmetricParameters.scalars cut 8
    0 (AsymmetricParameters.datum.α true) := fun δ =>
  (BalancedInduction.restriction
    (contentInclusion AsymmetricParameters.datum AsymmetricParameters.scalars cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable AsymmetricParameters.datum AsymmetricParameters.scalars cut 8
      ((oldTruncateFunctor AsymmetricParameters.datum AsymmetricParameters.scalars cut 8).obj ⟨[true]⟩))
private def oddShiftInput : ELVWeightProduct AsymmetricParameters.datum AsymmetricParameters.scalars cut 8
    0 (AsymmetricParameters.datum.α true) := fun δ => supermoduleParityObj (oddRawInput δ)
private def oddInputMap : oddShiftInput ⟶ oddRawInput := fun δ => (supermoduleParityIso (oddRawInput δ)).hom
private theorem oddInputMap_mem : oddInputMap ∈ parity (R := ℚ) _ _ 1 :=
  fun δ => supermoduleParityIso_hom_mem (oddRawInput δ)
local notation "χ" => elvWeightMixedMate AsymmetricParameters.datum AsymmetricParameters.scalars cut 8
  false true 0 oh₁ oh₂ oh₃ oh₄
local notation "hc" => elvWeightMixedMate_isIso AsymmetricParameters.datum AsymmetricParameters.scalars cut 8
  false true 0 oh₁ oh₂ oh₃ oh₄ (by decide)
example : AsymmetricParameters.datum.parity false * AsymmetricParameters.datum.parity true =
    (1 : ZMod 2) := rfl
example := let : IsIso χ := hc; (asIso χ).hom_inv_id
example := let : IsIso χ := hc; (asIso χ).inv_hom_id
/-- Odd inverse naturality retains the sign against the odd input map. -/
example := let : IsIso χ := hc; (inv χ).naturality 1 oddInputMap oddInputMap_mem
end OddMaps
end WeightMixedMateInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMateInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
