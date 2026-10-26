import OddMath.SKM.RouquierHomCrossing
/-!
# Removing parity comparisons from the normalized Hom mate

The input inverse and output comparison cancel in the defined mate, leaving
the raw cup, inherited crossing and normalized cap. This proves the sign
removal in `HomPrincipalMate.md` §2. The remaining even reassociation to
`leftCrossingWord`, and hence equation (10), is not asserted here.
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

/-- The defined normalized mate in raw coordinates. No shift comparison remains;
the crossing coefficient and cap normalization are retained in their components. -/
theorem homContentCrossing_coordinates_raw
    (Z : homWeightSector T.obj W nuP muM) :
    let P := homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))
    let P₂ := homParityShiftDatum (k := k) (leftAdjParity D i (-rhoP))
    T.E i h ◁ (P.iso (T.F i h ≫ Z)).inv ≫
      (rouquierMate (homContentSuperAdjunction T W i muM h)
        (homContentSuperAdjunction T W i muM h₂)
        (homContentCrossing T W i muM h h₂)).app (D.parity i) Z ≫
      (P₂.iso (T.F i h₂ ≫ T.E i h₂ ≫ Z)).hom =
    (leftUnitor (T.E i h ≫ T.F i h ≫ Z)).inv ≫
      T.leftCup i h₂ ▷ (T.E i h ≫ T.F i h ≫ Z) ≫
      (associator (T.F i h₂) (T.E i h₂) (T.E i h ≫ T.F i h ≫ Z)).hom ≫
      T.F i h₂ ◁ ((homContentCrossing T W i muM h h₂).app (D.parity i) (T.F i h ≫ Z) ≫
        T.E i h₂ ◁ ((associator (T.E i h) (T.F i h) Z).inv ≫
          ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k) • T.leftCap i h) ▷ Z ≫
          (leftUnitor Z).hom)) := by
  let σ := leftAdjParity D i (-nuP)
  let P := homParityShiftDatum (k := k) (C := T.obj (-muP) ⟶ W muM) σ
  let H := T.F i h ≫ Z
  let Q := T.E i h ≫ H
  let t := homContentCrossing T W i muM h h₂
  let A := homContentPreAdjunction T W T.leftAdjoints i muM h
  let A₂ := homContentPreAdjunction T W T.leftAdjoints i muM h₂
  let L₂ := homPre (k := k) (c := W muM) (T.E i h₂)
  let K₂ := homPre (k := k) (c := W muM) (T.F i h₂)
  let S₂ := homParityShift (k := k) (C := T.obj (-nuP) ⟶ W muM) (leftAdjParity D i (-rhoP))
  let f := T.E i h ◁ (P.iso H).inv
  let v := (associator (T.E i h) (T.F i h) Z).inv ≫
    ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k) • T.leftCap i h) ▷ Z ≫ (leftUnitor Z).hom
  have hfv : f ≫ A.counit.app Z = koszulSign σ σ • v := by
    dsimp only [A]
    rw [homContentPreAdjunction_leftAdjoints_counit_app]
    dsimp only [f, v, P, H, σ]
    rw [Preadditive.comp_zsmul]
    congr 1
    exact TwoSupercategory.whiskerLeft_inv_hom_assoc (R := k) _ _ _
  have ht := t.naturality (D.parity i) (P.iso H).inv (P.inv_mem H)
  change L₂.map f ≫ t.app (D.parity i) ((homContentPreF T W i muM h).obj Z) =
    koszulSign (D.parity i) σ • (t.app (D.parity i) H ≫ L₂.map f) at ht
  have hn := A₂.unit.naturality f
  change f ≫ A₂.unit.app _ = A₂.unit.app Q ≫ S₂.map (K₂.map (L₂.map f)) at hn
  let g := K₂.map (t.app (D.parity i) H ≫ L₂.map v)
  have hv : v ∈ parity (R := k) _ _ σ := by
    have hh := comp_mem (comp_mem
      (inv_mem (associator (T.E i h) (T.F i h) Z)
        (TwoSupercategory.associator_hom_mem (R := k) _ _ _))
      (TwoSupercategory.whiskerRight_mem Z
        (Submodule.smul_mem _ ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k)) (T.leftCap_mem i h))))
      (TwoSupercategory.leftUnitor_hom_mem (R := k) Z)
    simpa only [zero_add, add_zero, Category.assoc] using hh
  have hg : g ∈ parity (R := k) _ _ (D.parity i + σ) :=
    TwoSupercategory.whiskerLeft_mem _ (comp_mem (t.app_mem _ _) (TwoSupercategory.whiskerLeft_mem _ hv))
  have he : K₂.map (L₂.map f) ≫
      K₂.map (t.app (D.parity i) ((homContentPreF T W i muM h).obj Z)) ≫
      K₂.map (L₂.map (A.counit.app Z)) =
      (koszulSign (D.parity i) σ * koszulSign σ σ) • g := by
    rw [← K₂.map_comp, ← K₂.map_comp, ← Category.assoc, ht]
    simp only [Preadditive.zsmul_comp, Category.assoc]
    rw [← L₂.map_comp, hfv]
    simp only [Functor.map_zsmul, Preadditive.comp_zsmul, smul_smul, g]
  dsimp only
  rw [homContentSuperAdjunction_mate_app]
  simp only [Category.assoc]
  change f ≫ A₂.unit.app _ ≫ S₂.map (K₂.map (t.app (D.parity i) _)) ≫
    S₂.map (K₂.map (L₂.map (A.counit.app Z))) ≫ _ = _
  rw [reassoc_of% hn]
  rw [← S₂.map_comp_assoc, ← S₂.map_comp_assoc, Category.assoc]
  erw [he]
  rw [Functor.map_zsmul]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  erw [homContentPreAdjunction_unit_output_coordinates T W i muM h₂ Q _ g hg]
  simp only [smul_smul]
  have hp : (koszulSign (D.parity i) σ * koszulSign σ σ) *
      koszulSign (leftAdjParity D i (-rhoP)) (D.parity i + σ) = 1 := by
    rw [← leftAdjParity_edge D i h₂]
    change (koszulSign (D.parity i) σ * koszulSign σ σ) * koszulSign σ (D.parity i + σ) = 1
    exact (by decide : ∀ p q : ZMod 2,
      (koszulSign p q * koszulSign q q) * koszulSign q (p + q) = 1) (D.parity i) σ
  rw [hp, one_smul]
  rfl
end OddMath.SKM
