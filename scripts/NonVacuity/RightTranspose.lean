import OddMath.SKM.RouquierRightTranspose
import Lean.Util.CollectAxioms

/-!
Consumers of the derived right-transposition laws. Local Rouquier data are
assumed; these tests do not construct or assert a nonzero inversion model.
The two-dot odd cap detects the sign needed in the reflected inverse matrix.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-1)) :
    A₁.rightTranspose A₁ (x₁ ≫ x₁) =
      -(A₁.rightTranspose A₁ x₁ ≫ A₁.rightTranspose A₁ x₁) := by
  simpa using A₁.rightTranspose_comp A₁ A₁ L.dot₁_mem L.dot₁_mem

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 0) :
    rouquierPower (A₁.rightTranspose A₁ x₁) 2 ▷ E₁ ≫ A₁.counit = -L.capD 2 := by
  simpa using L.rightTranspose_capD 2

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-2)) :
    rouquierPower (A₁.rightTranspose A₁ x₁) 3 ▷ E₁ ≫ A₁.counit = -L.capD 3 := by
  simpa using L.rightTranspose_capD 3

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 2) (n : ℕ) :
    rouquierPower (A₁.rightTranspose A₁ x₁) n ▷ E₁ ≫ A₁.counit = L.capD n := by
  simpa using L.rightTranspose_capD n
end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierRightTranspose then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
