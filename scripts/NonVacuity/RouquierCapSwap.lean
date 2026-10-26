import OddMath.SKM.RouquierPitchfork
import Lean.Util.CollectAxioms

/-! Both-parity cap-swap consumers, including the local data extracted from a
Rouquier family. These are conditional type/sign checks, not a construction of
a nonzero odd inversion model. -/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
noncomputable section
section Local
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {A₃ : SuperAdjunction (k := k) E₃ F₃}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {t₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃}

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-1))
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ 0 1)  
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    U.capCross = -(L.capL ▷ E₂ ≫ (leftUnitor E₂).hom) +
      (associator E₂ F₂ E₂).hom ≫ E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom := by
  simpa using L.capCross_eq_of_neg U (by norm_num) (by norm_num) hsq hsq' hB

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-1))
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ 1 1)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    U.capCross = L.capL ▷ E₂ ≫ (leftUnitor E₂).hom -
      ((associator E₂ F₂ E₂).hom ≫ E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom) := by
  simpa [sub_eq_add_neg] using L.capCross_eq_of_neg U (by norm_num) (by norm_num) hsq hsq' hB
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-1))
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ 1 1)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (associator E₂ E₃ F₃).inv ≫ t₂₃ ▷ F₃ ≫ (associator E₂ E₃ F₃).hom ≫
      E₂ ◁ U.capL ≫ (rightUnitor E₂).hom = -
      (E₂ ◁ U.sigL ≫ (associator E₂ F₂ E₂).inv ≫ L.capL ▷ E₂ ≫
        (leftUnitor E₂).hom) := by
  simpa only [koszulSign_one_one, neg_one_zsmul] using
    L.capL_pitchfork_at_neg_one U (by norm_num) rfl hsq hsq' hB
end Local
section Family
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
example (T : RouquierFamily (k := k) (B := B) D) (i : I) {a b c d : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) (h₃ : c + D.α i = d)
    (hh : D.h i b < 0) :
    (T.loc i h₂ h₃).capCross = if D.h i b = -1 then koszulSign (D.parity i) (D.parity i) •
      (-((T.loc i h₁ h₂).capL ▷ T.E i h₂ ≫ (leftUnitor (T.E i h₂)).hom) +
        (associator (T.E i h₂) (T.F i h₂) (T.E i h₂)).hom ≫
        T.E i h₂ ◁ (T.adj i h₂).counit ≫ (rightUnitor (T.E i h₂)).hom)
      else -((T.loc i h₁ h₂).capL ▷ T.E i h₂ ≫ (leftUnitor (T.E i h₂)).hom) := by
  apply (T.loc i h₁ h₂).capCross_eq_of_neg (T.loc i h₂ h₃) _ hh
    (T.square i h₁ h₂) (T.square i h₂ h₃) (T.braid i h₁ h₂ h₃)
  rw [← h₂]
  simp [Datum.h, Datum.α, map_add, D.cd.coroot_root_self]
end Family

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierPitchfork then
      for n in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed {ax} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"
