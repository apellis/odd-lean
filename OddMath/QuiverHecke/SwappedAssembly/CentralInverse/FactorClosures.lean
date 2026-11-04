import OddMath.SKM.RouquierHomPostInverse
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ReservoirCoefficients

/-! # Factor inverse contractions as coefficient actions

SwappedHomInversion §4, equations (7)–(9): the content-shifted reservoir
principal closures and window boundaries are the post-whiskering actions
of the prescribed factor coefficients. The even source and target charts
cancel exactly. These equalities supply the coefficient-ideal attachment
for the chosen inverse, without grading the surrounding Hom morphisms.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath.SKM
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM rhoM : X}
  (h : muM + D.α i = nuM) (h₂ : nuM + D.α i = rhoM)

/-- The positive principal closure is the action of the specified factor closure. -/
theorem postCapInverse_closure (hh : 0 ≤ D.h i nuM)
    (Z : homWeightSector T W.obj muP nuM) (r s : ℕ) :
    homContentPostCup T W i betaP muP h₂ r Z ≫
      (homContentPostInvPos T W i betaP muP h h₂ hh Z).f' ≫
        homContentPostCap T W i betaP muP h s Z =
      ProbeWindow.postCoeff Z
        (((W.adj i h₂).unit ≫ rouquierPower (W.dot i h₂) r ▷ W.F i h₂) ≫
          ((W.loc i h h₂).invPos hh).f' ≫
            (W.F i h ◁ rouquierPower (W.dot i h) s ≫ (W.adj i h).counit)) := by
  rw [homContentPostCup_factor, homContentPostInvPos_principal, homContentPostCap_factor]
  simp only [ProbeWindow.postCoeff, TwoSupercategory.whiskerLeft_comp (R := k),
    Category.assoc, Iso.inv_hom_id_assoc]

/-- The negative principal has the same prescribed coefficient-action form. -/
theorem postCupInverse_closure (hh : D.h i nuM ≤ 0)
    (Z : homWeightSector T W.obj muP nuM) (r s : ℕ) :
    homContentPostCup T W i betaP muP h₂ r Z ≫
      (homContentPostInvNeg T W i betaP muP h h₂ hh Z).f' ≫
        homContentPostCap T W i betaP muP h s Z =
      ProbeWindow.postCoeff Z
        (((W.adj i h₂).unit ≫ rouquierPower (W.dot i h₂) r ▷ W.F i h₂) ≫
          ((W.loc i h h₂).invNeg hh).f' ≫
            (W.F i h ◁ rouquierPower (W.dot i h) s ≫ (W.adj i h).counit)) := by
  rw [homContentPostCup_factor, homContentPostInvNeg_principal, homContentPostCap_factor]
  simp only [ProbeWindow.postCoeff, TwoSupercategory.whiskerLeft_comp (R := k),
    Category.assoc, Iso.inv_hom_id_assoc]

/-- Every inverse cap-column contraction is the chosen positive boundary coefficient. -/
theorem postCapInverse_boundary (hh : 0 ≤ D.h i nuM)
    (Z : homWeightSector T W.obj muP nuM) (j r : ℕ) :
    (homContentPostInvPos T W i betaP muP h h₂ hh Z).g' j ≫
      homContentPostCap T W i betaP muP h r Z =
        ProbeWindow.postCoeff Z ((W.loc i h h₂).boundaryPos hh j r) := by
  rw [homContentPostInvPos_column, homContentPostCap_factor]
  simp only [ProbeWindow.postCoeff, SuperRouquierLoc.boundaryPos,
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc, Iso.inv_hom_id_assoc]

/-- Every unit-row inverse contraction is the chosen negative boundary coefficient. -/
theorem postCupInverse_boundary (hh : D.h i nuM ≤ 0)
    (Z : homWeightSector T W.obj muP nuM) (r j : ℕ) :
    homContentPostCup T W i betaP muP h₂ r Z ≫
      (homContentPostInvNeg T W i betaP muP h h₂ hh Z).g' j =
        ProbeWindow.postCoeff Z ((W.loc i h h₂).boundaryNeg hh r j) := by
  rw [homContentPostCup_factor, homContentPostInvNeg_row]
  simp only [ProbeWindow.postCoeff, SuperRouquierLoc.boundaryNeg,
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc, Iso.inv_hom_id_assoc]

end OddMath.QuiverHecke.SwappedAssembly
