/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRouquierMate
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMateInverse

/-! # The selected rank-one weight mate and its component formula

The principal field of Brundan–Ellis (1.13)–(1.14) is the local
Rouquier mate of the existing signed equal-colour crossing. It is the
same rectangular cup-crossing-cap used in the content matrix transport.
Its parity is p_i, and its lower and upper adjunctions remain those of
the prescribed adjacent weight steps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "A₁" => elvActionAdjunction D Sc cutoff bound i Λ h₁
local notation "A₂" => elvActionAdjunction D Sc cutoff bound i Λ h₂
local notation "Cross" => elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂

/-- The local-inversion principal entry is exactly the given rectangular weight mate. -/
theorem elvWeightRouquierMate_eq :
    SKM.rouquierMate A₁ A₂ Cross =
      elvWeightMixedMate D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ :=
  SKM.rouquierMate_piscat_eq_rectangular A₁ A₂ Cross

/-- The principal entry has the required rank-one matrix parity. -/
theorem elvWeightRouquierMate_mem :
    SKM.rouquierMate A₁ A₂ Cross ∈ parity (R := k) _ _ (D.parity i) := by
  rw [elvWeightRouquierMate_eq]
  simpa only [SKM.zmod2_mul_self] using
    elvWeightMixedMate_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂

end OddMath.QuiverHecke.ELVOld
