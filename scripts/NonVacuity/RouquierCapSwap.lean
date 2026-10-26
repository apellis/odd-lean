import OddMath.SKM.RouquierPitchfork
import Lean.Util.CollectAxioms

/-! Both-parity cup/cap-swap and canonical E-zigzag consumers, including the local data extracted from a
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
example (p : ZMod 2) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p (-2))
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ p 0)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (associator E₂ E₃ F₃).inv ≫ t₂₃ ▷ F₃ ≫ (associator E₂ E₃ F₃).hom ≫
      E₂ ◁ U.capL ≫ (rightUnitor E₂).hom =
      E₂ ◁ U.sigL ≫ (associator E₂ F₂ E₂).inv ≫ L.capL ▷ E₂ ≫
        (leftUnitor E₂).hom := by
  exact L.capL_pitchfork_below_neg_one U (by norm_num) (by norm_num) hsq hsq' hB
example (p : ZMod 2) (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ p (h + 2)) (hh : h < 0)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫
      L.capL ▷ E₂ ≫ (leftUnitor E₂).hom = 𝟙 E₂ :=
  L.leftAdj_triangle_E_of_neg U rfl hh hsq hsq' hB
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 0)
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ 0 2)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫
      L.capL ▷ E₂ ≫ (leftUnitor E₂).hom = 𝟙 E₂ := by
  simpa only [koszulSign_zero_left, one_smul] using
    L.leftAdj_triangle_E_of_nonneg U (by norm_num) (by norm_num) hsq hsq' hB
example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 h)
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ 0 (h + 2)) (hh : 0 < h)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫
      L.capL ▷ E₂ ≫ (leftUnitor E₂).hom = 𝟙 E₂ := by
  simpa only [koszulSign_zero_left, one_smul] using
    L.leftAdj_triangle_E_of_nonneg U rfl hh.le hsq hsq' hB
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 0)
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ 1 2)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫
      L.capL ▷ E₂ ≫ (leftUnitor E₂).hom = -𝟙 E₂ := by
  simpa only [koszulSign_one_one, neg_one_zsmul] using
    L.leftAdj_triangle_E_of_nonneg U (by norm_num) (by norm_num) hsq hsq' hB
example (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 h)
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ 1 (h + 2)) (hh : 0 < h)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫
      L.capL ▷ E₂ ≫ (leftUnitor E₂).hom = -𝟙 E₂ := by
  simpa only [koszulSign_one_one, neg_one_zsmul] using
    L.leftAdj_triangle_E_of_nonneg U rfl hh.le hsq hsq' hB
example (p : ZMod 2) (h : ℤ) (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ p (h + 2)) (hh : 0 < h)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (leftUnitor E₂).inv ≫ L.cupL ▷ E₂ ≫ (associator F₁ E₁ E₂).hom ≫
      F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv =
      (rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫ L.sigL ▷ E₂ := by
  simpa only [ite_eq_right (show h ≠ 0 by omega), one_smul] using
    L.cupL_pitchfork_of_nonneg U rfl hh.le hsq hsq' hB
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 0)
    (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t₂₃ 1 2)
    (hsq : t ≫ t = 0) (hsq' : t₂₃ ≫ t₂₃ = 0)
    (hB : E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t₂₃ =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t₂₃ ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (leftUnitor E₂).inv ≫ L.cupL ▷ E₂ ≫ (associator F₁ E₁ E₂).hom ≫
      F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv =
      -((rightUnitor E₂).inv ≫ E₂ ◁ U.cupL ≫ (associator E₂ F₂ E₂).inv ≫ L.sigL ▷ E₂) := by
  simpa only [ite_true, koszulSign_one_one, neg_one_zsmul] using
    L.cupL_pitchfork_of_nonneg U (by norm_num) (by norm_num) hsq hsq' hB
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
example (T : RouquierFamily (k := k) (B := B) D) (i : I) {a b c d : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) (h₃ : c + D.α i = d)
    (hh : D.h i b < -1) :
    (associator (T.E i h₂) (T.E i h₃) (T.F i h₃)).inv ≫ T.cross i i h₂ h₃ h₂ h₃ ▷ T.F i h₃ ≫
      (associator (T.E i h₂) (T.E i h₃) (T.F i h₃)).hom ≫
      T.E i h₂ ◁ (T.loc i h₂ h₃).capL ≫ (rightUnitor (T.E i h₂)).hom =
      T.E i h₂ ◁ (T.loc i h₂ h₃).sigL ≫
      (associator (T.E i h₂) (T.F i h₂) (T.E i h₂)).inv ≫
      (T.loc i h₁ h₂).capL ▷ T.E i h₂ ≫ (leftUnitor (T.E i h₂)).hom := by
  apply (T.loc i h₁ h₂).capL_pitchfork_below_neg_one (T.loc i h₂ h₃) _ hh
    (T.square i h₁ h₂) (T.square i h₂ h₃) (T.braid i h₁ h₂ h₃)
  rw [← h₂]
  simp [Datum.h, Datum.α, map_add, D.cd.coroot_root_self]
example (T : RouquierFamily (k := k) (B := B) D) (i : I) {x y : X}
    (e : x + D.α i = y) (hh : D.h i x < 0) : T.leftZigE i e = 𝟙 (T.E i e) :=
  T.leftZigE_of_neg i e hh
example (T : RouquierFamily (k := k) (B := B) D) (i : I) {x y : X}
    (e : x + D.α i = y) (hh : 0 ≤ D.h i x) :
    T.leftZigE i e = koszulSign (D.parity i) (D.parity i) • 𝟙 (T.E i e) :=
  T.leftZigE_of_nonneg i e hh
example (T : RouquierFamily (k := k) (B := B) D) (i : I) {x y : X}
    (e : x + D.α i = y) :
    T.leftZigE i e = (if D.h i x < 0 then 1 else koszulSign (D.parity i) (D.parity i)) • 𝟙 (T.E i e) :=
  T.leftZigE_eq i e
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
