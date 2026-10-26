import OddMath.SKM.RouquierHorizontalReflection
import Lean.Util.CollectAxioms

/-!
The reflected mate agrees with the inverse partial bend on arbitrary maps,
and with the prescribed original mate on the transpose of an odd crossing.
Rational odd local data are premises; no nonzero model is asserted here.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
section
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  (A₁ : SuperAdjunction (k := ℚ) E₁ F₁) (A₂ : SuperAdjunction (k := ℚ) E₂ F₂)
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

example (v : F₂ ≫ F₁ ⟶ F₂ ≫ F₁) :
    rouquierMate A₁.horizontalOpposite A₂.horizontalOpposite v =
      (mixedMateBend A₁ A₂).symm v :=
  rouquierMate_horizontalOpposite A₁ A₂ v

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    rouquierMate A₁.horizontalOpposite A₂.horizontalOpposite
      ((A₁.comp A₂).rightTranspose (A₁.comp A₂) t) = rouquierMate A₁ A₂ t ∧
    (A₁.comp A₂).rightTranspose (A₁.comp A₂) t ∈ parity (R := ℚ) _ _ 1 := by
  constructor
  · rw [rouquierMate_horizontalOpposite, mixedMateBend_symm_rightTranspose]
  · exact SuperAdjunction.rightTranspose_mem _ _ L.cross_mem
end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierHorizontalReflection then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
