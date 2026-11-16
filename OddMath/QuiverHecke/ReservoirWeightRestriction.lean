import OddMath.QuiverHecke.ReservoirWeights
import OddMath.SKM.RouquierData

/-! # Restriction from the pairing-complete weight lattice

The fixed-weight transport accompanying the balancing arithmetic in
`Categorification/KLR/Unfurling/GenericWeights.lean`.
A super Rouquier factor family on the extended weight lattice restricts to
the original datum. No pairing-surjectivity assumption on the original
lattice is introduced. This transports local factor inversion, not the
unproved separated-sector fusion or full multicolour presentation.
-/
noncomputable section
namespace OddMath.QuiverHecke.ReservoirWeights
open CategoryTheory StringDiagrams
universe u v w r
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)

/-- The original weight embedding preserves each root edge. -/
theorem extension_edge (i : I) {x y : X} (h : x + D.α i = y) :
    (x, (0 : I → ℤ)) + (pairingExtension D).α i = (y, 0) := by
  apply Prod.ext
  · exact h
  · exact add_zero 0

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- Restrict a factor family along `μ ↦ (μ,0)`. All homogeneous inverse
components, including their parity shifts, are inherited unchanged. -/
def restrictRouquierFamily
    (F : SKM.RouquierFamily (k := k) (B := B) (pairingExtension D)) :
    SKM.RouquierFamily (k := k) (B := B) D where
  obj := fun x => F.obj (x, 0)
  E := fun i {_ _} h => F.E i (extension_edge D i h)
  dot := fun i {_ _} h => F.dot i (extension_edge D i h)
  dot_mem := fun i {_ _} h => F.dot_mem i (extension_edge D i h)
  cross := fun i j {_ _ _ _} h₁ h₂ h₃ h₄ => F.cross i j
    (extension_edge D j h₁) (extension_edge D i h₂)
    (extension_edge D i h₃) (extension_edge D j h₄)
  cross_mem := fun i j {_ _ _ _} h₁ h₂ h₃ h₄ => F.cross_mem i j
    (extension_edge D j h₁) (extension_edge D i h₂)
    (extension_edge D i h₃) (extension_edge D j h₄)
  F := fun i {_ _} h => F.F i (extension_edge D i h)
  adj := fun i {_ _} h => F.adj i (extension_edge D i h)
  square := fun i {_ _ _} h₁ h₂ => F.square i (extension_edge D i h₁) (extension_edge D i h₂)
  braid := fun i {_ _ _ _} h₁ h₂ h₃ => F.braid i
    (extension_edge D i h₁) (extension_edge D i h₂) (extension_edge D i h₃)
  loc := fun i {_ _ _} h₁ h₂ => by
    simpa only [show (pairingExtension D).parity i = D.parity i from rfl,
      pairingExtension_h, Pi.zero_apply, add_zero] using
      F.loc i (extension_edge D i h₁) (extension_edge D i h₂)

@[simp] theorem restrictRouquierFamily_obj
    (F : SKM.RouquierFamily (k := k) (B := B) (pairingExtension D)) (μ : X) :
    (restrictRouquierFamily D F).obj μ = F.obj (μ, 0) := rfl

end OddMath.QuiverHecke.ReservoirWeights
