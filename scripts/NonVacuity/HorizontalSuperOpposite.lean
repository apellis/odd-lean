import OddMath.SKM.HorizontalSuperOpposite
import OddMath.SKM.RouquierRightTranspose
import Lean.Util.CollectAxioms

/-!
Reflection of the right adjunctions in rational, odd local Rouquier data.
The local data are premises, not an asserted nonzero model. The reflected
category retains degree-one dots and the negative odd–odd interchange.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
section
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  (A₁ : SuperAdjunction (k := ℚ) E₁ F₁) (A₂ : SuperAdjunction (k := ℚ) E₂ F₂)
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

example : TwoSupercategory ℚ (HOpS B) := inferInstance

example : A₁.horizontalOpposite.unit = A₁.unit ∧
    A₁.horizontalOpposite.counit = A₁.counit := ⟨rfl, rfl⟩

example : (leftUnitor (B := HOpS B) (a := ⟨a⟩) (b := ⟨b⟩) F₁).inv ≫
    BicategoryStruct.whiskerRight (B := HOpS B) A₁.horizontalOpposite.unit F₁ ≫
    (associator (B := HOpS B) F₁ E₁ F₁).hom ≫
    BicategoryStruct.whiskerLeft (B := HOpS B) F₁ A₁.horizontalOpposite.counit ≫
    (rightUnitor (B := HOpS B) F₁).hom = 𝟙 F₁ :=
  A₁.horizontalOpposite.left_triangle

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    A₁.rightTranspose A₁ x₁ ∈ parity (R := ℚ)
      (show (⟨a⟩ : HOpS B) ⟶ ⟨b⟩ from F₁) F₁ 1 :=
  SuperAdjunction.rightTranspose_mem A₁ A₁ L.dot₁_mem

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    TwoSupercategory.hcomp (B := HOpS B)
      (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩)
      (A₁.rightTranspose A₁ x₁) (A₂.rightTranspose A₂ x₂) =
    -(BicategoryStruct.whiskerLeft (B := HOpS B) F₁ (A₂.rightTranspose A₂ x₂) ≫
      BicategoryStruct.whiskerRight (B := HOpS B) (A₁.rightTranspose A₁ x₁) F₂) := by
  simpa only [koszulSign_one_one, neg_one_smul] using
    (TwoSupercategory.hcomp_eq (B := HOpS B)
      (SuperAdjunction.rightTranspose_mem A₁ A₁ L.dot₁_mem)
      (SuperAdjunction.rightTranspose_mem A₂ A₂ L.dot₂_mem))
end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.HorizontalSuperOpposite then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
