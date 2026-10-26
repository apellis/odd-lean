import OddMath.SKM.RouquierTransposeWhiskering
import Lean.Util.CollectAxioms

/-!
Whiskered odd dots retain degree one, and the reversed associator has both
composite adjunctions explicit. Local data remain premises, not a nonzero model.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
section
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  {A₁ : SuperAdjunction (k := ℚ) E₁ F₁} {A₂ : SuperAdjunction (k := ℚ) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    (A₁.comp A₂).rightTranspose (A₁.comp A₂) (E₁ ◁ x₂) =
      A₂.rightTranspose A₂ x₂ ▷ F₁ ∧
    (A₁.comp A₂).rightTranspose (A₁.comp A₂) (E₁ ◁ x₂) ∈
      parity (R := ℚ) _ _ 1 :=
  ⟨SuperAdjunction.rightTranspose_whiskerLeft A₁ A₂ A₂ x₂,
    SuperAdjunction.rightTranspose_mem _ _ (TwoSupercategory.whiskerLeft_mem E₁ L.dot₂_mem)⟩

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    (A₁.comp A₂).rightTranspose (A₁.comp A₂) (x₁ ▷ E₂) =
      F₂ ◁ A₁.rightTranspose A₁ x₁ ∧
    (A₁.comp A₂).rightTranspose (A₁.comp A₂) (x₁ ▷ E₂) ∈
      parity (R := ℚ) _ _ 1 :=
  ⟨SuperAdjunction.rightTranspose_whiskerRight A₁ A₁ A₂ x₁,
    SuperAdjunction.rightTranspose_mem _ _ (TwoSupercategory.whiskerRight_mem E₂ L.dot₁_mem)⟩

example (A₃ : SuperAdjunction (k := ℚ) E₃ F₃) :
    (A₁.comp (A₂.comp A₃)).rightTranspose ((A₁.comp A₂).comp A₃)
      (associator E₁ E₂ E₃).inv = (associator F₃ F₂ F₁).inv :=
  SuperAdjunction.rightTranspose_associator_inv A₁ A₂ A₃
end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierTransposeWhiskering then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
