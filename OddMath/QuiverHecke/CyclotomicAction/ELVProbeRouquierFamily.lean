import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightNilHecke
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierData

/-! # The chosen OLD probe Rouquier family on original weights

Brundan–Ellis Definition 1.5 and (1.8)–(1.14): assemble the chosen scalar-
evaluated induction, restriction, signed dots and crossings with the
constructed local inverse families. The cutoff matches the highest
weight. No local inverse or factor-family premise is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

/-- The selected weight maps form the local Rouquier record at the categorical height. -/
def probeOldWeightLoc (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) :
    SKM.SuperRouquierLoc (probeOldActionAdjunction D Sc m i Λ h₁)
      (probeOldActionAdjunction D Sc m i Λ h₂)
      (probeOldActionDot D Sc m i Λ h₁) (probeOldActionDot D Sc m i Λ h₂)
      (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂) (D.parity i) (D.h i x₁) where
  dot₁_mem := probeOldActionDot_mem D Sc m i Λ h₁
  dot₂_mem := probeOldActionDot_mem D Sc m i Λ h₂
  cross_mem := by
    simpa only [SKM.zmod2_mul_self] using probeOldActionCross_mem D Sc m Λ i i h₁ h₂ h₁ h₂
  slide_left := by
    rw [probeOldActionCross_equal]
    exact probeOldActionEqualCross_slideLeft D Sc m i Λ h₁ h₂
  slide_right := by
    rw [probeOldActionCross_equal]
    exact probeOldActionEqualCross_slideRight D Sc m i Λ h₁ h₂
  invPos hh := Classical.choice (probeOldWeightLocalCapFamily_nonempty D Sc m i Λ h₁ h₂ hcutoff hh)
  invNeg hh := Classical.choice (probeOldWeightLocalUnitFamily_nonempty D Sc m i Λ h₁ h₂ hcutoff hh)

variable (hcutoff : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)

/-- The chosen probe generators, prescribed right adjunctions and constructed inverses. -/
def probeOldRouquierFamily :
    SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u + 1} k) D where
  toRouquierData := probeOldRouquierData D Sc m Λ
  F i _ _ h := probeOldF D Sc m i Λ h
  adj i _ _ h := probeOldActionAdjunction D Sc m i Λ h
  square i _ _ _ h₁ h₂ := probeOldRouquierData_square D Sc m Λ i h₁ h₂
  braid i _ _ _ _ h₁ h₂ h₃ := probeOldRouquierData_braid D Sc m Λ i h₁ h₂ h₃
  loc i _ _ _ h₁ h₂ := probeOldWeightLoc D Sc m i Λ h₁ h₂ (hcutoff i)

/-- The chosen dot remains a unit on the assembled probe family. -/
theorem probeOldRouquierFamily_dot_isUnit [Fintype I] (i : I) {x y : X} (h : x + D.α i = y) :
    IsUnit (End.of ((probeOldRouquierFamily D Sc m Λ hcutoff).dot i h)) :=
  probeOldRouquierData_dot_isUnit D Sc m Λ i h

end OddMath.QuiverHecke
