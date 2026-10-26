import OddMath.SKM.RouquierCompositeAdjunction
import Lean.Util.CollectAxioms

/-!
Consumers of the derived right-transposition laws. Local Rouquier data are
assumed; these tests do not construct or assert a nonzero inversion model.
The composite adjunction is used on an odd crossing at arbitrary height.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

example : (A₁.comp A₂).unit = A₁.unit ≫ E₁ ◁ (leftUnitor F₁).inv ≫
    E₁ ◁ (A₂.unit ▷ F₁) ≫ E₁ ◁ (associator E₂ F₂ F₁).hom ≫
    (associator E₁ E₂ (F₂ ≫ F₁)).inv := A₁.comp_unit A₂

example : (A₁.comp A₂).counit = (associator F₂ F₁ (E₁ ≫ E₂)).hom ≫
    F₂ ◁ (associator F₁ E₁ E₂).inv ≫ F₂ ◁ (A₁.counit ▷ E₂) ≫
    F₂ ◁ (leftUnitor E₂).hom ≫ A₂.counit := A₁.comp_counit A₂

example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h) :
    (A₁.comp A₂).rightTranspose (A₁.comp A₂) t ∈ parity (R := k) _ _ 1 :=
  (A₁.comp A₂).rightTranspose_mem (A₁.comp A₂) L.cross_mem

example : (A₁.comp A₂).rightTranspose (A₁.comp A₂) t ▷ (E₁ ≫ E₂) ≫
    (A₁.comp A₂).counit = (F₂ ≫ F₁) ◁ t ≫ (A₁.comp A₂).counit :=
  (A₁.comp A₂).rightTranspose_counit (A₁.comp A₂) t

example : (A₁.comp A₂).unit ≫ t ▷ (F₂ ≫ F₁) =
    (A₁.comp A₂).unit ≫ (E₁ ≫ E₂) ◁
      (A₁.comp A₂).rightTranspose (A₁.comp A₂) t :=
  ((A₁.comp A₂).rightTranspose_unit (A₁.comp A₂) t).symm

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierCompositeAdjunction then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"
