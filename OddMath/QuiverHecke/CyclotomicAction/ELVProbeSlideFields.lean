import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierData
import OddMath.QuiverHecke.CyclotomicAction.ELVParameterUntwist

/-! # Exact distinct slide fields of the bundled OLD probe generators

Brundan–Ellis (1.8): retain the actual bundled crossing and the two
independently chosen whiskered dots in the literal RouquierMulticolour
slideLeft/slideRight formats. These follow from the proved whole-weight
slides, including their absent-predecessor components. No partial action
record or assumed slide relation is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Sc'" => parameterTwist D Sc
local notation "T" => probeOldRouquierData D Sc' m Λ

/-- The exact left slide for the actual bundled distinct crossing. -/
theorem probeOldRouquierData_slideLeft (hij : i ≠ j) :
    (T).E j h₁ ◁ (T).dot i h₂ ≫ (T).cross i j h₁ h₂ h₃ h₄ =
      SKM.zsign k (D.parity i * D.parity j) •
        ((T).cross i j h₁ h₂ h₃ h₄ ≫ (T).dot i h₃ ▷ (T).E j h₄) := by
  dsimp only [probeOldRouquierData]
  rw [probeOldActionCross_distinct D Sc' m Λ i j hij]
  have h := probeOldActionDistinctCross_slide_inner D Sc' m i j Λ h₁ h₂ h₃ h₄ hij
  have hs := congrArg (fun f => sign k (D.parity i * D.parity j) • f) h
  simp only [Supercategory.sign_smul_sign_smul] at hs
  simpa only [sign_eq_zsign] using hs.symm

/-- The exact right slide, with the same original generator choices and parity sign. -/
theorem probeOldRouquierData_slideRight (hij : i ≠ j) :
    (T).cross i j h₁ h₂ h₃ h₄ ≫ (T).E i h₃ ◁ (T).dot j h₄ =
      SKM.zsign k (D.parity i * D.parity j) •
        ((T).dot j h₁ ▷ (T).E i h₂ ≫ (T).cross i j h₁ h₂ h₃ h₄) := by
  dsimp only [probeOldRouquierData]
  rw [probeOldActionCross_distinct D Sc' m Λ i j hij]
  simpa only [sign_eq_zsign] using
    probeOldActionDistinctCross_slide_outer D Sc' m i j Λ h₁ h₂ h₃ h₄ hij
end OddMath.QuiverHecke
