import OddMath.SKM.RouquierReflectedLocal
import Lean.Util.CollectAxioms

/-!
Reflection at odd parity over ℚ, including both zero-height inverses and the
negative sign in the second dotted window. Local data are premises; this
consumer does not assert existence of a nonzero odd local inversion model.
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
    SuperRouquierLoc A₁.horizontalOpposite A₂.horizontalOpposite
      (A₁.rightTranspose A₁ x₁) (A₂.rightTranspose A₂ x₂) L.reflectedCross 1 h :=
  L.horizontalReflection

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 0) :
    (L.horizontalReflection.invPos (by decide)).f' = -(L.invPos (by decide)).f' ∧
    (L.horizontalReflection.invNeg (by decide)).f' = -(L.invNeg (by decide)).f' := by
  constructor
  · simpa using L.horizontalReflection_invPos_f' (by decide)
  · simpa using L.horizontalReflection_invNeg_f' (by decide)

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 3) :
    (L.horizontalReflection.invPos (by decide)).g' 2 = -(L.invPos (by decide)).g' 2 := by
  simpa using L.horizontalReflection_invPos_g' (by decide) 2

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-3)) :
    (L.horizontalReflection.invNeg (by decide)).g' 2 = -(L.invNeg (by decide)).g' 2 := by
  simpa using L.horizontalReflection_invNeg_g' (by decide) 2

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 2) :
    L.horizontalReflection.boundaryPos (by decide) 0 1 = 0 := by
  exact L.horizontalReflection.boundaryPos_eq (by decide) 0 1 (by decide) (by decide)

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-2)) :
    L.horizontalReflection.boundaryNeg (by decide) 1 1 = 𝟙 _ := by
  simpa using L.horizontalReflection.boundaryNeg_eq (by decide) 1 1 (by decide) (by decide)

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) (ht : t ≫ t = 0) :
    L.reflectedCross ≫ L.reflectedCross = 0 := L.reflectedCross_square ht
end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierReflectedLocal then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
