import OddMath.SKM.RouquierFTriangle

/-!
# Fixed normalized reservoir Hom adjunction

The canonical triangles supply the fixed cup and inverse-scaled cap. The existing
content-shifted Hom adjunction therefore needs no additional left-zigzag premise.
The unit is reduced to its cup and output-shift comparison. The counit is reduced
to the signed normalized cap of `HomSectorTransport.md`, §2, by homogeneous
comparison naturality and cancellation of the shift-square and commuting maps.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
section Shift
variable {k : Type r} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Supercategory k C] [PiSupercategory k C]

theorem homParityShiftAdjunction_counit_app (p : ZMod 2) (Z : C) :
    (homParityShiftAdjunction (k := k) p).counit.app Z =
      (homParityShiftSquare (k := k) p).hom.app Z := by
  rcases (show p = 0 ∨ p = 1 by fin_cases p; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl <;>
    simp [homParityShiftAdjunction, homParityShiftSquare, homParityShiftAdd,
      homParityShift, homPiAdjunction]

theorem homParityShiftSquare_hom_app (p : ZMod 2) (Z : C) :
    (homParityShiftSquare (k := k) p).hom.app Z =
      (koszulSign p p : ℤ) •
        (((homParityShiftDatum (k := k) p).iso
          ((homParityShift (k := k) p).obj Z)).hom ≫
          ((homParityShiftDatum (k := k) p).iso Z).hom) := by
  rcases (show p = 0 ∨ p = 1 by fin_cases p; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl
  · simp [homParityShiftSquare, homParityShiftAdd, homParityShiftDatum,
      homParityShift, ParityShiftDatum.id]
  · simpa [homParityShiftSquare, homParityShiftAdd, homParityShiftDatum,
      homParityShift, ParityShiftDatum.pi] using PiSupercategory.ξ_hom_eq_neg (R := k) Z

theorem homParityShiftSquare_inv_map_even (p : ZMod 2) (X Z : C)
    (g : (homParityShift (k := k) p).obj X ⟶ (homParityShift (k := k) p).obj Z)
    (hg : g ∈ parity (R := k) _ _ 0) :
    (homParityShiftSquare (k := k) p).inv.app X ≫
      (homParityShift (k := k) p).map g ≫ (homParityShiftSquare (k := k) p).hom.app Z =
      ((homParityShiftDatum (k := k) p).iso X).inv ≫ g ≫
        ((homParityShiftDatum (k := k) p).iso Z).hom := by
  apply (cancel_epi ((homParityShiftSquare (k := k) p).hom.app X)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [homParityShiftSquare_hom_app, homParityShiftSquare_hom_app]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  rw [reassoc_of% ((homParityShiftDatum (k := k) p).hom_naturality_even hg)]
  simp only [Iso.hom_inv_id_assoc]

variable {C' : Type*} [Category C'] [Preadditive C'] [Linear k C']
  [Supercategory k C'] [PiSupercategory k C']

theorem homParityShiftCommute_inv_app (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) (Z : C) :
    (homParityShiftCommute (k := k) F p).inv.app Z =
      F.map ((homParityShiftDatum (k := k) p).iso Z).hom ≫
        ((homParityShiftDatum (k := k) p).iso (F.obj Z)).inv := by
  rcases (show p = 0 ∨ p = 1 by fin_cases p; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl
  · change 𝟙 (F.obj Z) ≫ 𝟙 (F.obj Z) = F.map (𝟙 Z) ≫ 𝟙 (F.obj Z)
    rw [F.map_id]
  · rfl
theorem homParityShiftCommute_hom_app (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) (Z : C) :
    (homParityShiftCommute (k := k) F p).hom.app Z =
      ((homParityShiftDatum (k := k) p).iso (F.obj Z)).hom ≫
        F.map ((homParityShiftDatum (k := k) p).iso Z).inv := by
  apply (cancel_mono ((homParityShiftCommute (k := k) F p).inv.app Z)).mp
  rw [Iso.hom_inv_id_app, homParityShiftCommute_inv_app]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map _), ← F.map_comp, Iso.inv_hom_id, F.map_id,
    Category.id_comp, Iso.hom_inv_id]

end Shift

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP : X} (h : -nuP + D.α i = -muP)

theorem homContentPreAdjunction_unit_app
    (L : RouquierLeftAdjoints (k := k) T) (Z : homWeightSector T.obj W muP muM) :
    (homContentPreAdjunction T W L i muM h).unit.app Z =
      (leftUnitor Z).inv ≫ (L.adjL i h).unit ▷ Z ≫
        (associator (T.F i h) (T.E i h) Z).hom ≫
        ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
          (T.F i h ≫ T.E i h ≫ Z)).inv := by
  simp only [homContentPreAdjunction, Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Adjunction.comp_unit_app]
  dsimp only [homContentPreE, homContentPreF, homWeightSector]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Functor.comp_map, Functor.comp_obj, Iso.symm_hom]
  change ((homPreShiftUnitApp (L.adjL i h) _ Z ≫
    T.F i h ◁ (homParityShiftAdjunction (k := k) (leftAdjParity D i (-nuP))).unit.app
      ((homParityShift (k := k) (leftAdjParity D i (-nuP))).obj (T.E i h ≫ Z))) ≫
      T.F i h ◁ (homParityShift (k := k) (leftAdjParity D i (-nuP))).map
        ((homParityShiftSquare (k := k) (leftAdjParity D i (-nuP))).hom.app
          (T.E i h ≫ Z) ≫ 𝟙 _)) ≫
      (homParityShiftCommute (homPre (k := k) (T.F i h))
        (leftAdjParity D i (-nuP))).inv.app (T.E i h ≫ Z) = _
  rw [Category.comp_id]
  rw [← homParityShiftAdjunction_counit_app]
  simp only [Category.assoc]
  rw [← Category.assoc (T.F i h ◁ _), ← (TwoSupercategory.whiskerLeft_comp (R := k)),
    Adjunction.right_triangle_components,
    (TwoSupercategory.whiskerLeft_id (R := k)), Category.id_comp, homParityShiftCommute_inv_app]
  change homPreShiftUnitApp (L.adjL i h) _ Z ≫
    ((homPre (k := k) (T.F i h)).map _ ≫ _) = _
  simp only [homPreShiftUnitApp, homPre, Category.assoc]
  rw [(TwoSupercategory.whiskerLeft_inv_hom_assoc (R := k))]

/-- Specialization to the canonical family: no separate left-triangle input. -/
theorem homContentPreAdjunction_leftAdjoints_unit_app
    (Z : homWeightSector T.obj W muP muM) :
    (homContentPreAdjunction T W T.leftAdjoints i muM h).unit.app Z =
      (leftUnitor Z).inv ≫ T.leftCup i h ▷ Z ≫
        (associator (T.F i h) (T.E i h) Z).hom ≫
        ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
          (T.F i h ≫ T.E i h ≫ Z)).inv :=
  homContentPreAdjunction_unit_app T W i muM h T.leftAdjoints Z

/-- The counit of the specified adjunction, retaining the shift-square and
commuting comparison. This is an expansion, not yet the reduced signed-cap formula. -/
theorem homContentPreAdjunction_leftAdjoints_counit_expansion
    (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z =
      T.E i h ◁ (homParityShiftCommute (homPre (k := k) (T.F i h))
        (leftAdjParity D i (-nuP))).hom.app Z ≫
      (homParityShiftSquare (k := k) (leftAdjParity D i (-nuP))).inv.app
        (T.E i h ≫ T.F i h ≫
          (homParityShift (k := k) (leftAdjParity D i (-nuP))).obj Z) ≫
      (homParityShift (k := k) (leftAdjParity D i (-nuP))).map
        (((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
          (T.E i h ≫ T.F i h ≫
            (homParityShift (k := k) (leftAdjParity D i (-nuP))).obj Z)).hom ≫
          (associator (T.E i h) (T.F i h)
            ((homParityShift (k := k) (leftAdjParity D i (-nuP))).obj Z)).inv ≫
          ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k) • T.leftCap i h) ▷
            ((homParityShift (k := k) (leftAdjParity D i (-nuP))).obj Z) ≫
          (leftUnitor ((homParityShift (k := k) (leftAdjParity D i (-nuP))).obj Z)).hom) ≫
      (homParityShiftSquare (k := k) (leftAdjParity D i (-nuP))).hom.app Z := by
  simp only [homContentPreAdjunction, Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Adjunction.comp_counit_app]
  dsimp only [homContentPreE, homContentPreF, homWeightSector]
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Functor.comp_obj, Iso.symm_inv]
  change _ ≫ (_ ≫ 𝟙 _) ≫ _ ≫ _ = _
  rw [Category.comp_id, homParityShiftAdjunction_counit_app]
  rfl
/-- The signed-cap component of the specified normalized adjunction
(`HomSectorTransport.md`, §2, equation (4)). -/
theorem homContentPreAdjunction_leftAdjoints_counit_app
    (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z =
      koszulSign (leftAdjParity D i (-nuP)) (leftAdjParity D i (-nuP)) •
        (T.E i h ◁ ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
          (T.F i h ≫ Z)).hom ≫
          (associator (T.E i h) (T.F i h) Z).inv ≫
          ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k) • T.leftCap i h) ▷ Z ≫
          (leftUnitor Z).hom) := by
  let p := leftAdjParity D i (-nuP)
  let P := homParityShiftDatum (k := k) (C := T.obj (-nuP) ⟶ W muM) p
  let S := homParityShift (k := k) (C := T.obj (-nuP) ⟶ W muM) p
  let A := T.leftAdjoints.adjL i h
  rw [homContentPreAdjunction_leftAdjoints_counit_expansion]
  change T.E i h ◁ (homParityShiftCommute (homPre (k := k) (T.F i h)) p).hom.app Z ≫
    (homParityShiftSquare (k := k) p).inv.app (T.E i h ≫ T.F i h ≫ S.obj Z) ≫
    S.map (homPreShiftCounitApp A P (S.obj Z)) ≫
    (homParityShiftSquare (k := k) p).hom.app Z =
      koszulSign p p •
        (T.E i h ◁ ((homParityShiftDatum (k := k) p).iso (T.F i h ≫ Z)).hom ≫
          (associator (T.E i h) (T.F i h) Z).inv ≫ A.counit ▷ Z ≫ (leftUnitor Z).hom)
  rw [homParityShiftSquare_inv_map_even p _ Z _ (homPreShiftCounitApp_mem A P _)]
  have hn := (homPreShiftCounit A P).naturality (P.iso Z).hom
  change S.map (T.E i h ◁ T.F i h ◁ (P.iso Z).hom) ≫ homPreShiftCounitApp A P Z =
    homPreShiftCounitApp A P (S.obj Z) ≫ (P.iso Z).hom at hn
  rw [← hn]
  unfold homPreShiftCounitApp
  rw [reassoc_of% (P.hom_naturality
    (TwoSupercategory.whiskerLeft_mem (T.E i h)
      (TwoSupercategory.whiskerLeft_mem (T.F i h) (P.hom_mem Z))))]
  dsimp only [P]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [homParityShiftCommute_hom_app]
  simp only [homPre, TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [← Category.assoc (T.E i h ◁ T.F i h ◁ _),
    ← TwoSupercategory.whiskerLeft_comp (R := k),
    ← TwoSupercategory.whiskerLeft_comp (R := k), Iso.inv_hom_id,
    TwoSupercategory.whiskerLeft_id (R := k), TwoSupercategory.whiskerLeft_id (R := k),
    Category.id_comp]
  rw [koszulSign_smul (R := k)]

end OddMath.SKM
