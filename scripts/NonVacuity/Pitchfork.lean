import OddMath.SKM.RouquierPitchfork

/-!
Odd-parity, concrete-height specializations of the curl inputs to the pitchfork proof.
These are signature checks assuming local Rouquier data, not a construction of a
nonzero categorical model of those data.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM

section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

/-- At odd parity and height zero, one intervening dot gives `+1`. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 0) (hsq : t ≫ t = 0) :
    curlEG A₂.unit L.capL (t ≫ rouquierPower x₁ 1 ▷ E₂ ≫ t) = 𝟙 E₁ := by
  have := L.curlEG_double_dotted hsq (n := 1) (by omega) (by omega)
  simpa [koszulSign] using this

/-- At odd parity and height minus one, two intervening dots give `-1`. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-1)) (hsq : t ≫ t = 0) :
    curlEG A₂.unit L.capL (t ≫ rouquierPower x₁ 2 ▷ E₂ ≫ t) = -𝟙 E₁ := by
  have := L.curlEG_double_dotted hsq (n := 2) (by omega) (by omega)
  simpa [koszulSign] using this

/-- Moving one dot to the cup remains below the height minus two boundary. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-2)) :
    curlEG (L.cupD 1) L.capL t = 0 := L.curlEG_cupD_zero (by omega)
end

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierPitchfork then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  logInfo m!"Audited {count} owned declarations"
