import OddMath.SKM.RouquierCurl

/-!
Consumers for the super curl calculus (Brundan, Lemma 4.1). At an odd colour with `h > 0`
the boundary right curl is `+1` (the signed slide contributes `s = -1`), at `h = 0` it is
`-1`; the boundary left curl is `1` at every parity. Signature/axiom check.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM

section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

/-- Odd colour, `h = 1`: the boundary right curl is `+1`. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 1) :
    curlG L.cupL (L.capD 1) t = 𝟙 E₂ := by
  have := L.curlG_capD_self (by omega)
  simpa [koszulSign] using this

/-- Odd colour, `h = 0`: the boundary right curl is `-1`. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 0) :
    curlG L.cupL (L.capD 0) t = -𝟙 E₂ := by
  have := L.curlG_capD_self le_rfl
  simpa using this

/-- Odd colour, `h = -2`: the boundary left curl is `1`. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-2)) :
    curlEG (L.cupD 2) L.capL t = 𝟙 E₁ :=
  L.curlEG_cupD_self (by omega)

/-- Odd colour, `h = 2`: one dot below the boundary gives a vanishing right curl. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 2) :
    curlG (L.cupL ≫ F₁ ◁ rouquierPower x₁ 1) A₁.counit t = 0 := by
  have := L.curlG_dotted (n := 1) (by omega)
  simpa using this
end

#print axioms SuperRouquierLoc.curlG_dotted
#print axioms SuperRouquierLoc.curlEG_dotted
#print axioms SuperRouquierLoc.curlG_capD_self
#print axioms SuperRouquierLoc.curlEG_cupD_self
#print axioms SuperRouquierLoc.sig_counit_pitchfork
#print axioms SuperRouquierLoc.unit_sig_pitchfork
