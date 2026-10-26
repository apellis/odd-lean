import OddMath.SKM.RouquierMateProjection

/-! Interface checks for the two parity specializations of the mate obligation.
These do not assert that the Hom-sector construction satisfies the obligation. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) {XA XB YA YB : b ⟶ b}
  (inA : XA ⟶ F₁ ≫ E₁) (inB : XB ⟶ F₁ ≫ E₁)
  (outA : E₂ ≫ F₂ ⟶ YA) (outB : E₂ ≫ F₂ ⟶ YB)
  (uA : ℕ → (𝟙 b ⟶ YA)) (vA : ℕ → (XA ⟶ 𝟙 b))
  (uB : ℤ → (𝟙 b ⟶ YB)) (vB : ℤ → (XB ⟶ 𝟙 b)) (nC nD : ℕ)

example (h : SuperRouquierLoc.MateProjectionFormula A₁ A₂ t 1
    inA inB outA outB uA vA uB vB nC nD) :
    inB ≫ rouquierMate A₁ A₂ t ≫ outA =
      ∑ r ∈ Finset.range nC, (-1 : ℤ) ^ r • (vB (-(r : ℤ) - 1) ≫ uA r) := by
  simpa using h.1

example (h : SuperRouquierLoc.MateProjectionFormula A₁ A₂ t 0
    inA inB outA outB uA vA uB vB nC nD) :
    inA ≫ (-rouquierMate A₁ A₂ t) ≫ outB =
      -(∑ r ∈ Finset.range nD, vA r ≫ uB (-(r : ℤ) - 1)) := by
  simpa using h.2

#print axioms SuperRouquierLoc.MateProjectionFormula
