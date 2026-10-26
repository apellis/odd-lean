import OddMath.SKM.RouquierInverseRelations

/-!
Consumers for the inverse-matrix relations of super Rouquier data, applied to the
local data of a Rouquier family at positive and negative `⟨hᵢ, λ⟩`. This is a
signature/axiom check; no concrete family is constructed here.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM

section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}

example (T : RouquierFamily (k := k) (B := B) D) (i : I) {a b c : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) (hh : 0 < D.h i b) :
    (T.loc i h₁ h₂).ccw (D.h i b - 1) = 𝟙 _ ∧ (T.loc i h₁ h₂).cupL ≫ (T.loc i h₁ h₂).sig = 0 :=
  ⟨SuperRouquierLoc.ccw_self hh, SuperRouquierLoc.cupL_sig hh⟩

example (T : RouquierFamily (k := k) (B := B) D) (i : I) {a b c : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) (hh : D.h i b < 0) :
    (T.loc i h₁ h₂).cw (-D.h i b - 1) = 𝟙 _ ∧ (T.loc i h₁ h₂).sig ≫ (T.loc i h₁ h₂).capL = 0 :=
  ⟨SuperRouquierLoc.cw_self hh, SuperRouquierLoc.sig_capL hh⟩

example (T : RouquierFamily (k := k) (B := B) D) (i : I) {a b c : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) (hh : D.h i b = 0) :
    (T.loc i h₁ h₂).sig ≫ (T.loc i h₁ h₂).sigL = -𝟙 _ ∧
      (T.loc i h₁ h₂).sigL ≫ (T.loc i h₁ h₂).sig = -𝟙 _ :=
  ⟨SuperRouquierLoc.sig_sigL_of_nonpos hh.le, SuperRouquierLoc.sigL_sig_of_nonneg hh.ge⟩
end

#print axioms SuperRouquierLoc.sigL_of_nonpos
#print axioms SuperRouquierLoc.sig_sigL_of_nonneg
#print axioms SuperRouquierLoc.sigL_sig_of_nonpos
#print axioms SuperRouquierLoc.ccw_self
#print axioms SuperRouquierLoc.cw_of_lt
