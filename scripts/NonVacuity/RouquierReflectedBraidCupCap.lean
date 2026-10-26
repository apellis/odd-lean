import OddMath.SKM.RouquierReflectedBraid
import OddMath.SKM.RouquierReflectedCupCap
import Lean.Util.CollectAxioms

/-! Odd-parity, arbitrary-integer-height consumers. Local data are premises;
no nonzero odd inversion model is asserted by these comparisons. -/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
section
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  {A₁ : SuperAdjunction (k := ℚ) E₁ F₁} {A₂ : SuperAdjunction (k := ℚ) E₂ F₂}
  {A₃ : SuperAdjunction (k := ℚ) E₃ F₃}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {t' : E₂ ≫ E₃ ⟶ E₂ ≫ E₃}

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    L.horizontalReflection.cupL =
      (if 0 < h then (-1 : ℤ) ^ ((h - 1).toNat.choose 2)
       else -((-1 : ℤ) ^ ((-h).toNat.choose 2))) • L.cupL := by
  simpa using L.horizontalReflection_cupL

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    L.horizontalReflection.capL =
      (if h < 0 then (-1 : ℤ) ^ ((-h - 1).toNat.choose 2)
       else -((-1 : ℤ) ^ (h.toNat.choose 2))) • L.capL := by
  simpa using L.horizontalReflection_capL

example (h h' : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h)
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t' 1 h')
    (hb : E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
        (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t' =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
        E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
          (associator E₁ E₂ E₃).hom)) :
    U.reflectedCross ▷ F₁ ≫ ((associator F₃ F₂ F₁).hom ≫ F₃ ◁ L.reflectedCross ≫
        (associator F₃ F₂ F₁).inv) ≫ U.reflectedCross ▷ F₁ =
      ((associator F₃ F₂ F₁).hom ≫ F₃ ◁ L.reflectedCross ≫
        (associator F₃ F₂ F₁).inv) ≫ U.reflectedCross ▷ F₁ ≫
      ((associator F₃ F₂ F₁).hom ≫ F₃ ◁ L.reflectedCross ≫
        (associator F₃ F₂ F₁).inv) := L.reflectedCross_braid U hb
end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if #[`OddMath.SKM.RouquierReflectedBraid,
        `OddMath.SKM.RouquierReflectedCupCap].contains env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
