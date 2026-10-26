import OddMath.SKM.RouquierDotSlide

/-!
Consumers for the signed dot slides through the rightward crossing. At an even
colour the Koszul sign is `1` and the formula is Brundan's (2.3); at an odd
colour two dots pass with sign `+1` and one with `-1`. Signature/axiom check.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM

section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}

/-- Odd colour, one dot: the crossing anticommutes with the dot up to the cap–cup. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    F₁ ◁ x₁ ≫ L.sig = -(L.sig ≫ x₂ ▷ F₂) + L.capD 0 ≫ L.cupD 0 := by
  rw [L.dot_sig]
  simp [koszulSign]

/-- Odd colour, two dots: the leading term has sign `+1`. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    F₁ ◁ rouquierPower x₁ 2 ≫ L.sig = L.sig ≫ rouquierPower x₂ 2 ▷ F₂ -
      (L.capD 0 ≫ L.cupD 1 - L.capD 1 ≫ L.cupD 0) := by
  rw [L.powComp_sig 2]
  simp [koszulSign, Finset.sum_range_succ, sub_eq_add_neg]

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 h) (hh : 0 < h) :
    L.cupL ≫ F₁ ◁ rouquierPower x₁ 0 ≫ L.sig = 0 :=
  L.cupL_powComp_sig hh (by omega)
/-- Even colour, `h = 0`, `t = 2`: Brundan's relation `P_0 Q_0 + P_(-1) Q_1 + P_1 Q_(-1) = 0`. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 0) :
    L.ccw 0 ≫ L.cw 0 + L.ccw (-1) ≫ L.cw 1 + L.ccw 1 ≫ L.cw (-1) = 0 := by
  have := L.infGrass_nonneg le_rfl 1
  simpa [koszulSign] using this
/-- Odd colour, `h = 0`, `t = 2`, from the `h ≤ 0` side:
`-P_0 Q_0 + P_1 Q_(-1) - P_(-1) Q_1 = 0`, matching the `h ≥ 0` side. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 0) :
    -(L.ccw 0 ≫ L.cw 0) + L.ccw 1 ≫ L.cw (-1) - L.ccw (-1) ≫ L.cw 1 = 0 := by
  have := L.infGrass_nonpos le_rfl 1
  simp [koszulSign] at this
  rw [← this]
  abel

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 0) :
    -(L.ccw 0 ≫ L.cw 0) - L.ccw (-1) ≫ L.cw 1 + L.ccw 1 ≫ L.cw (-1) = 0 := by
  have := L.infGrass_nonneg le_rfl 1
  simp [koszulSign] at this
  rw [← this]
  abel
end

#print axioms SuperRouquierLoc.infGrass_nonpos
#print axioms SuperRouquierLoc.infGrass_nonneg
#print axioms SuperRouquierLoc.powComp_sig
#print axioms SuperRouquierLoc.cupL_powComp_sig
#print axioms SuperRouquierLoc.sig_capL_expansion
#print axioms SuperRouquierLoc.cupL_sig_expansion
