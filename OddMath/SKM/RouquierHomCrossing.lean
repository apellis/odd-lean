import OddMath.SKM.RouquierHomSuperAdjunction

/-!
# Inherited crossing on normalized Hom sectors

The prescribed crossing is minus the same-colour Koszul sign times the
reassociated reservoir crossing. Its mate is formed with the normalized Hom
adjunctions, for the principal comparison in `HomPrincipalMate.md`, §2.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP rhoP : X}
  (h : -nuP + D.α i = -muP) (h₂ : -rhoP + D.α i = -nuP)

/-- The inherited same-colour crossing, with the horizontal-reversal coefficient. -/
def homContentCrossing :
    homContentSuperE T W i muM h ≫ homContentSuperE T W i muM h₂ ⟶
      homContentSuperE T W i muM h ≫ homContentSuperE T W i muM h₂ :=
  ((SuperNatTrans.ofNatTrans (homPreComp (T.E i h₂) (T.E i h)).hom
      (fun Z => inv_mem (associator _ _ Z)
        (TwoSupercategory.associator_hom_mem (R := k) _ _ Z))).vcomp
      (homPreTransform ((-koszulSign (D.parity i) (D.parity i)) • T.cross i i h₂ h h₂ h)
        (zsmul_mem (T.loc i h₂ h).cross_mem _))).vcomp
    (SuperNatTrans.ofNatTrans (homPreComp (T.E i h₂) (T.E i h)).inv
      (fun Z => TwoSupercategory.associator_hom_mem (R := k) _ _ Z))

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Every parity component of the prescribed crossing in reservoir coordinates. -/
theorem homContentCrossing_app (q : ZMod 2)
    (Z : homWeightSector T.obj W muP muM) :
    (homContentCrossing T W i muM h h₂).app q Z =
      if q = D.parity i then (-koszulSign (D.parity i) (D.parity i)) •
        ((associator (T.E i h₂) (T.E i h) Z).inv ≫
          T.cross i i h₂ h h₂ h ▷ Z ≫ (associator (T.E i h₂) (T.E i h) Z).hom)
      else 0 := by
  fin_cases q <;> rcases parity_eq_zero_or_one (D.parity i) with hp | hp <;>
    simp [homContentCrossing, SuperNatTrans.ofNatTrans, homPreTransform,
      homPreComp, hp, Category.assoc]
  all_goals
    simp [TwoSupercategory.neg_whiskerRight (R := k)]

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The prescribed crossing has the colour parity. -/
theorem homContentCrossing_mem : homContentCrossing T W i muM h h₂ ∈
    parity (R := k) _ _ (D.parity i) := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.2
  intro q hq
  funext Z
  simp [homContentCrossing_app, hq]

/-- The normalized mate of the inherited crossing, with the output-shifted
lowering functors and both specified adjunction components expanded. -/
theorem homContentCrossing_mate_app
    (Z : homWeightSector T.obj W nuP muM) :
    let P := homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))
    let P₂ := homParityShiftDatum (k := k) (leftAdjParity D i (-rhoP))
    let H := (homContentPreF T W i muM h).obj Z
    let Q := T.E i h ≫ H
    (rouquierMate (homContentSuperAdjunction T W i muM h)
      (homContentSuperAdjunction T W i muM h₂)
      (homContentCrossing T W i muM h h₂)).app (D.parity i) Z =
      ((leftUnitor Q).inv ≫ T.leftCup i h₂ ▷ Q ≫
        (associator (T.F i h₂) (T.E i h₂) Q).hom ≫
        (P₂.iso (T.F i h₂ ≫ T.E i h₂ ≫ Q)).inv) ≫
      (homContentPreF T W i muM h₂).map
        ((-koszulSign (D.parity i) (D.parity i)) •
          ((associator (T.E i h₂) (T.E i h) H).inv ≫
            T.cross i i h₂ h h₂ h ▷ H ≫
            (associator (T.E i h₂) (T.E i h) H).hom)) ≫
      (homContentPreF T W i muM h₂).map ((homContentPreE T W i muM h₂).map
        (koszulSign (leftAdjParity D i (-nuP)) (leftAdjParity D i (-nuP)) •
          (T.E i h ◁ (P.iso (T.F i h ≫ Z)).hom ≫
            (associator (T.E i h) (T.F i h) Z).inv ≫
            ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k) • T.leftCap i h) ▷ Z ≫
            (leftUnitor Z).hom))) := by
  dsimp only
  rw [homContentSuperAdjunction_mate_app, homContentCrossing_app, ite_eq_left rfl,
    homContentPreAdjunction_leftAdjoints_unit_app,
    homContentPreAdjunction_leftAdjoints_counit_app]
  rfl

end OddMath.SKM
