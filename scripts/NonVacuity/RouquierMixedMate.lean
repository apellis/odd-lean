import OddMath.SKM.RouquierMixedMate
import Lean.Util.CollectAxioms

/-! Typed consumers of the rectangular transpose and the odd interchange.
The supercategory and adjunctions remain explicit parameters: this is not a
construction of a nonzero inversion model or a proof of the mixed braid. -/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
noncomputable section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (A₃ : SuperAdjunction (k := k) E₃ F₃)

example (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    rouquierMate A₁ A₂ t ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom =
    (associator F₁ E₁ E₂).hom ≫ F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫
      A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom := rouquierMate_pitchfork_cap A₁ A₂ t

example (t₁₂ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (t₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃)
    (h₁₂ : t₁₂ ∈ parity (R := k) _ _ 1) (h₂₃ : t₂₃ ∈ parity (R := k) _ _ 1) :
    rouquierMate A₁ A₂ t₁₂ ▷ (E₂ ≫ E₃) ≫ (E₂ ≫ F₂) ◁ t₂₃ =
      -((F₁ ≫ E₁) ◁ t₂₃ ≫ rouquierMate A₁ A₂ t₁₂ ▷ (E₂ ≫ E₃)) := by
  simpa only [koszulSign_one_one, neg_one_zsmul] using
    rouquierMate_cross_interchange A₁ A₂ h₁₂ h₂₃

example (z : (E₁ ≫ E₂) ≫ E₃ ⟶ E₁ ≫ (E₂ ≫ E₃)) :
    (rectangularMate A₁ A₃ (E₁ ≫ E₂) (E₂ ≫ E₃)).symm
      (rectangularMate A₁ A₃ (E₁ ≫ E₂) (E₂ ≫ E₃) z) = z :=
  Equiv.symm_apply_apply _ z

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierMixedMate then
      for n in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed {ax} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"
