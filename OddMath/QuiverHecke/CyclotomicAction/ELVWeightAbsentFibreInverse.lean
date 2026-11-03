/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightAbsentUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightInverseProducts

/-! # Weight unit inverses over all absent predecessor blocks

BE (1.14): assemble the prescribed component inverses on the product of
all output blocks without a lower predecessor. The window is the same
categorical height on the whole weight fibre, with no finite-support or
root-injectivity condition.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "Absent" => {δ : WeightBlocks D Λ x₁ // ¬ ∃ β, blockSucc D Λ i h₁ β = δ}
local notation "F₂" => elvF D Sc cutoff N i Λ h₂
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)

/-- The prescribed inverse exists simultaneously at every absent output block;
its finite window is the height of the weight, independent of the block. -/
theorem elvWeightAbsentFibreInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    Nonempty (SKM.SuperSumInvFrom (k := k)
      (show (fun δ : Absent => ((elvF D Sc cutoff N i Λ h₁ ≫
        elvE D Sc cutoff N i Λ h₁).obj M) δ.1) ⟶
        (fun δ : Absent => ((elvE D Sc cutoff N i Λ h₂ ≫ F₂).obj M) δ.1)
        from fun δ => (φ).app (D.parity i) M δ.1)
      (fun n => (show (fun δ : Absent => M δ.1) ⟶
        (fun δ : Absent => ((elvE D Sc cutoff N i Λ h₂ ≫ F₂).obj M) δ.1)
        from fun δ => (elvActionUnit D Sc cutoff N i Λ h₂ ≫
          SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂).total M δ.1))
      (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
  exact ⟨SKM.SuperSumInvFrom.pi (fun δ => Classical.choice
    (elvWeightAbsentUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ δ.1 hcutoff δ.2 M))⟩

end OddMath.QuiverHecke.ELVOld
