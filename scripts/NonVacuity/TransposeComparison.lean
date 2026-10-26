import OddMath.SKM.RouquierTransposeComparison
import Lean.Util.CollectAxioms

/-!
The comparison is exercised at odd parity and arbitrary integral height.
Local inversion data remain premises; no nonzero representation is asserted.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
section
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := ℚ) E₁ F₁} {A₂ : SuperAdjunction (k := ℚ) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    mixedMateBend A₁ A₂ (rouquierMate A₁ A₂ t) =
      (A₁.comp A₂).rightTranspose (A₁.comp A₂) t ∧
    mixedMateBend A₁ A₂ (rouquierMate A₁ A₂ t) ∈ parity (R := ℚ) _ _ 1 := by
  constructor
  · exact mixedMateBend_rouquierMate A₁ A₂ t
  · rw [mixedMateBend_rouquierMate]
    exact (A₁.comp A₂).rightTranspose_mem (A₁.comp A₂) L.cross_mem

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    (mixedMateBend A₁ A₂).symm ((A₁.comp A₂).rightTranspose (A₁.comp A₂) t) =
      rouquierMate A₁ A₂ t ∧ rouquierMate A₁ A₂ t ∈ parity (R := ℚ) _ _ 1 :=
  ⟨mixedMateBend_symm_rightTranspose A₁ A₂ t, rouquierMate_parity A₁ A₂ L.cross_mem⟩

example (u : F₁ ≫ E₁ ⟶ E₂ ≫ F₂) :
    (mixedMateBend A₁ A₂).symm (mixedMateBend A₁ A₂ u) = u :=
  (mixedMateBend A₁ A₂).symm_apply_apply u

example (v : F₂ ≫ F₁ ⟶ F₂ ≫ F₁) :
    mixedMateBend A₁ A₂ ((mixedMateBend A₁ A₂).symm v) = v :=
  (mixedMateBend A₁ A₂).apply_symm_apply v
end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if #[`OddMath.SKM.RouquierTransposeComparison, `OddMath.SKM.RouquierMixedMate].contains
        env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
