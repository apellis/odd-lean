/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentRectangularCross

/-! # Supported weight coordinates for the distinct mate

The source and target of the weight mate of Brundan–Ellis (1.12) are
identified with their literal four-corner content induction/restriction
coordinates. The common upper content is the actual j-successor of the
output block, with the i-successor comparison kept explicit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- A chosen predecessor determines induction at an arbitrary literal target block. -/
theorem elvInductionComponent_obj_of (i : I) (Λ : X) {x y : X}
    (h : x + D.α i = y) (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y)
    (hβ : blockSucc D Λ i h β = δ) (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M =
      BalancedInduction.induced
        (contentAppendTo D Sc cutoff bound β.1 [i] δ.1
          ((elvBlockSucc_content_eq D i Λ h β).trans (congrArg Subtype.val hβ))) (M β) := by
  subst δ
  exact elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M

variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "J" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "U" => elvBlockAppend D Sc cutoff bound j Λ h₄ (blockSucc D Λ i h₃ β)

include h₂ in
/-- The two successor orders have this same literal upper content. -/
theorem elvMixedUpper_content_eq :
    (blockSucc D Λ j h₁ β).1 + ([i] : Multiset I) =
      (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)).1 :=
  (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β)).trans
    (congrArg Subtype.val (blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β))

local notation "L" => contentAppendTo D Sc cutoff bound (Subtype.val (blockSucc D Λ j h₁ β)) [i]
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β))) (elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β)

/-- The actual supported source is induction of the restricted input at its predecessor. -/
theorem elvWeightMixedSource_obj (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (((elvF D Sc cutoff bound j Λ h₁ ≫ elvE D Sc cutoff bound i Λ h₃).obj M) δi) =
      BalancedInduction.induced K ((BalancedInduction.restriction J).obj (M δj)) :=
  elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β
    ((elvF D Sc cutoff bound j Λ h₁).obj M)

/-- The actual supported target is restriction of induction to the same upper content. -/
theorem elvWeightMixedTarget_obj (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (((elvE D Sc cutoff bound i Λ h₂ ≫ elvF D Sc cutoff bound j Λ h₄).obj M) δi) =
      (BalancedInduction.restriction U).obj (BalancedInduction.induced L (M δj)) := by
  exact congrArg (fun P => (BalancedInduction.restriction U).obj P)
    (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε
      (blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β) M)

end OddMath.QuiverHecke.ELVOld
