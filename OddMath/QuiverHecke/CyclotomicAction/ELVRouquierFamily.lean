/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightRouquierLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightBraid

/-! # The ELV Rouquier family on the original weight group

Brundan–Ellis Definition 1.5, (1.8)–(1.14): assemble the prescribed
induction, restriction, dots, same-colour crossings and constructed local
inverses. The cutoff matches the highest weight. The separate multicolour
relations are still required for an action of the complete presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)

/-- The chosen weight functors and their constructed local inverses.
There is no local-inverse or factor-family premise. -/
def elvRouquierFamily :
    SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u + 1} k) D where
  toRouquierData := elvRouquierData D Sc cutoff bound Λ
  F i _ _ h := elvF D Sc cutoff bound i Λ h
  adj i _ _ h := elvActionAdjunction D Sc cutoff bound i Λ h
  square i _ _ _ h₁ h₂ := elvRouquierData_square D Sc cutoff bound i Λ h₁ h₂
  braid i _ _ _ _ h₁ h₂ h₃ := elvRouquierData_braid D Sc cutoff bound i Λ h₁ h₂ h₃
  loc i _ _ _ h₁ h₂ := Classical.choice
    (elvWeightRouquierLocal_nonempty D Sc cutoff bound i Λ h₁ h₂ (hcutoff i))

/-- Restriction is the prescribed right adjoint at each original weight. -/
theorem elvRouquierFamily_F (i : I) {x y : X} (h : x + D.α i = y) :
    (elvRouquierFamily D Sc cutoff bound Λ hcutoff).F i h =
      elvF D Sc cutoff bound i Λ h := rfl

end OddMath.QuiverHecke.ELVOld
