import OddMath.SKM.RouquierHomSuperAdjunction

/-!
# Content-shifted postcomposition coordinates

The specified adjunction is bundled in `SCat`, keeping the shift on the input
of the right adjoint. The BB crossing uses the canonical beta/xi comparison.
Its factor crossing commutes with the two parity removals: the two homogeneous
signs cancel. Unit and counit coordinates are proved for the specified
adjunction. These are inputs to `HomProbeMatrix.md` (B); the complete principal
mate comparison with the factor mixed mate is not proved here.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
section Shift
variable {k : Type r} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Supercategory k C] [PiSupercategory k C]

theorem homParityShiftAdjunction_unit_app (p : ZMod 2) (Z : C) :
    (homParityShiftAdjunction (k := k) p).unit.app Z =
      (homParityShiftSquare (k := k) p).inv.app Z := by
  rcases (show p = 0 ∨ p = 1 by fin_cases p; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl <;>
    simp [homParityShiftAdjunction, homParityShiftSquare, homParityShiftAdd,
      homParityShift, homPiAdjunction]

theorem homParityShiftSquare_mem (p : ZMod 2) (Z : C) :
    (homParityShiftSquare (k := k) p).hom.app Z ∈ parity (R := k) _ _ 0 := by
  rw [homParityShiftSquare_hom_app]
  apply zsmul_mem
  simpa only [zmod2_add_self, Functor.comp_obj, Functor.id_obj] using comp_mem
    ((homParityShiftDatum (k := k) p).hom_mem _)
    ((homParityShiftDatum (k := k) p).hom_mem _)

theorem homParityShiftSquare_inv_mem (p : ZMod 2) (Z : C) :
    (homParityShiftSquare (k := k) p).inv.app Z ∈ parity (R := k) _ _ 0 :=
  inv_mem ((homParityShiftSquare (k := k) p).app Z) (homParityShiftSquare_mem p Z)

theorem homParityShiftSquare_hom_app_map (p : ZMod 2) (Z : C) :
    (homParityShiftSquare (k := k) p).hom.app Z =
      (homParityShift (k := k) p).map ((homParityShiftDatum (k := k) p).iso Z).hom ≫
        ((homParityShiftDatum (k := k) p).iso Z).hom := by
  rcases (show p = 0 ∨ p = 1 by fin_cases p; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl
  · simp [homParityShiftSquare, homParityShiftAdd, homParityShiftDatum,
      homParityShift, ParityShiftDatum.id]
  · simpa [homParityShiftSquare, homParityShiftAdd, homParityShiftDatum,
      homParityShift, ParityShiftDatum.pi] using PiSupercategory.ξ_hom (R := k) Z

variable {C' : Type u} [Category.{v} C'] [Preadditive C'] [Linear k C']
  [Supercategory k C'] [PiSupercategory k C']

/-- The prescribed beta/xi removal of the two shifts around a superfunctor. -/
def homShiftConjugationIso (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) (Z : C) :
    (homParityShift (k := k) p).obj (F.obj ((homParityShift (k := k) p).obj Z)) ≅
      F.obj Z :=
  (homParityShift (k := k) p).mapIso ((homParityShiftCommute (k := k) F p).app Z).symm ≪≫
    (homParityShiftSquare (k := k) p).app (F.obj Z)

/-- Expanding the prescribed beta/xi comparison cancels the middle inverse pair. -/
theorem homShiftConjugationIso_hom (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) (Z : C) :
    (homShiftConjugationIso F p Z).hom =
      (homParityShift (k := k) p).map
        (F.map ((homParityShiftDatum (k := k) p).iso Z).hom) ≫
      ((homParityShiftDatum (k := k) p).iso (F.obj Z)).hom := by
  change (homParityShift (k := k) p).map ((homParityShiftCommute (k := k) F p).inv.app Z) ≫
    (homParityShiftSquare (k := k) p).hom.app (F.obj Z) = _
  rw [homParityShiftCommute_inv_app, homParityShiftSquare_hom_app_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((homParityShift (k := k) p).map
    ((homParityShiftDatum (k := k) p).iso (F.obj Z)).inv),
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Each of the two homogeneous comparisons contributes the same sign; their
product is one, for either transformation parity and either content shift. -/
theorem homShiftConjugationIso_supernatural
    (F G : C ⥤ C') [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    (p q : ZMod 2) (t : ∀ Z, F.obj Z ⟶ G.obj Z)
    (ht : IsSupernatural k q t) (Z : C) :
    (homParityShift (k := k) p).map (t ((homParityShift (k := k) p).obj Z)) ≫
      (homShiftConjugationIso G p Z).hom =
    (homShiftConjugationIso F p Z).hom ≫ t Z := by
  rw [homShiftConjugationIso_hom, homShiftConjugationIso_hom,
    ← Functor.map_comp_assoc]
  have ht' : t ((homParityShift (k := k) p).obj Z) ≫
      G.map ((homParityShiftDatum (k := k) p).iso Z).hom =
      sign k (q * p) • (F.map ((homParityShiftDatum (k := k) p).iso Z).hom ≫ t Z) := by
    rw [ht.naturality ((homParityShiftDatum (k := k) p).hom_mem Z),
      smul_smul, sign_mul_self, one_smul]
  rw [ht']
  rw [Functor.map_smul, Functor.map_comp, Linear.smul_comp, Category.assoc,
    ((homParityShiftDatum (k := k) p).hom_naturality (ht.mem Z)),
    Linear.comp_smul, smul_smul, mul_comm q p, sign_mul_self, one_smul,
    Category.assoc]

/-- The two removals have the signed normalization used by the sector coordinates. -/
theorem homShiftConjugationIso_hom_signed (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) (Z : C) :
    (homShiftConjugationIso F p Z).hom = sign k (p * p) •
      (((homParityShiftDatum (k := k) p).iso
        (F.obj ((homParityShift (k := k) p).obj Z))).hom ≫
        F.map ((homParityShiftDatum (k := k) p).iso Z).hom) := by
  rw [homShiftConjugationIso_hom]
  exact (homParityShiftDatum (k := k) p).hom_naturality
    (map_mem F ((homParityShiftDatum (k := k) p).hom_mem Z))

variable {C'' : Type u} [Category.{v} C''] [Preadditive C''] [Linear k C'']
  [Supercategory k C''] [PiSupercategory k C'']

/-- Factoring the two-shift comparison keeps the canonical beta on the outer functor. -/
theorem homShiftConjugationIso_comp (F : C ⥤ C') (G : C' ⥤ C'')
    [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G] (p : ZMod 2) (Z : C) :
    (homShiftConjugationIso (F ⋙ G) p Z).hom =
      (homParityShiftCommute G p).hom.app (F.obj ((homParityShift (k := k) p).obj Z)) ≫
        G.map (homShiftConjugationIso F p Z).hom := by
  rw [homShiftConjugationIso_hom_signed, homShiftConjugationIso_hom_signed,
    homParityShiftCommute_hom_app, Functor.map_smul, Linear.comp_smul,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc (G.map ((homParityShiftDatum (k := k) p).iso
    (F.obj ((homParityShift (k := k) p).obj Z))).inv),
    ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]
  rfl

/-- The even natural isomorphism underlying the prescribed two-shift removal. -/
def homShiftConjugationNatIso (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) :
    (homParityShift (k := k) p ⋙ F) ⋙ homParityShift (k := k) p ≅ F :=
  Functor.isoWhiskerRight (homParityShiftCommute (k := k) F p).symm (homParityShift (k := k) p) ≪≫
    Functor.associator F _ _ ≪≫ Functor.isoWhiskerLeft F (homParityShiftSquare p) ≪≫
    Functor.rightUnitor F

theorem homShiftConjugationNatIso_hom_app (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) (Z : C) :
    (homShiftConjugationNatIso (k := k) F p).hom.app Z = (homShiftConjugationIso (k := k) F p Z).hom := by
  simp [homShiftConjugationNatIso, homShiftConjugationIso]

theorem homShiftConjugationIso_mem (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) (Z : C) :
    (homShiftConjugationIso (k := k) F p Z).hom ∈ parity (R := k) _ _ 0 := by
  rw [homShiftConjugationIso_hom_signed]
  apply Submodule.smul_mem
  simpa only [zmod2_add_self] using comp_mem
    ((homParityShiftDatum (k := k) p).hom_mem _)
    (map_mem F ((homParityShiftDatum (k := k) p).hom_mem Z))

theorem homShiftConjugationIso_id (p : ZMod 2) (Z : C) :
    (homShiftConjugationIso (k := k) (𝟭 C) p Z).hom =
      (homParityShiftSquare (k := k) p).hom.app Z := by
  rw [homShiftConjugationIso_hom, homParityShiftSquare_hom_app_map]
  rfl

/-- The square comparison commutes with the parity shift. -/
theorem homParityShiftSquare_shift (p : ZMod 2) (Z : C) :
    (homParityShiftSquare (k := k) p).hom.app ((homParityShift (k := k) p).obj Z) =
      (homParityShift (k := k) p).map ((homParityShiftSquare (k := k) p).hom.app Z) := by
  rcases (show p = 0 ∨ p = 1 by fin_cases p; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl
  · simp [homParityShiftSquare, homParityShiftAdd, homParityShift]
  · simpa [homParityShiftSquare, homParityShiftAdd, homParityShift] using
      PiSupercategory.ξ_pi (R := k) Z

/-- The inner shift-square from the specified unit cancels the shifted word comparison. -/
theorem homShiftConjugationIso_unit_cancel (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) (Z : C) :
    (homParityShiftSquare (k := k) p).inv.app (F.obj ((homParityShift (k := k) p).obj Z)) ≫
      (homParityShift (k := k) p).map (homShiftConjugationIso F p Z).hom =
        (homParityShiftCommute (k := k) F p).inv.app Z := by
  change (homParityShiftSquare (k := k) p).inv.app _ ≫
    (homParityShift (k := k) p).map
      ((homParityShift (k := k) p).map ((homParityShiftCommute (k := k) F p).inv.app Z) ≫
        (homParityShiftSquare (k := k) p).hom.app _) = _
  rw [Functor.map_comp]
  have hn := (homParityShiftSquare (k := k) p).inv.naturality
    ((homParityShiftCommute (k := k) F p).inv.app Z)
  change (homParityShiftCommute (k := k) F p).inv.app Z ≫ (homParityShiftSquare (k := k) p).inv.app _ =
    (homParityShiftSquare (k := k) p).inv.app _ ≫
      (homParityShift (k := k) p).map
        ((homParityShift (k := k) p).map ((homParityShiftCommute (k := k) F p).inv.app Z)) at hn
  rw [← Category.assoc, ← hn, Category.assoc, ← homParityShiftSquare_shift,
    Iso.inv_hom_id_app]
  change (homParityShiftCommute (k := k) F p).inv.app Z ≫
    𝟙 ((F ⋙ homParityShift (k := k) p).obj Z) = _
  exact Category.comp_id _

end Shift

section Hom
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM)

def homContentPostSuperE : SCat.of k (homWeightSector T W.obj muP muM) ⟶
    SCat.of k (homWeightSector T W.obj muP nuM) :=
  ⟨homContentPostE T W i betaP muP h⟩

def homContentPostSuperF : SCat.of k (homWeightSector T W.obj muP nuM) ⟶
    SCat.of k (homWeightSector T W.obj muP muM) :=
  ⟨homContentPostF T W i betaP muP h⟩

theorem homContentPostAdjunction_unit_mem (Z : homWeightSector T W.obj muP muM) :
    (homContentPostAdjunction T W i betaP muP h).unit.app Z ∈
      parity (R := k) _ _ 0 := by
  change ((homPostAdjunction (W.adj i h)).comp
    (homParityShiftAdjunction (homContentShift D i betaP))).unit.app Z ∈ _
  rw [Adjunction.comp_unit_app, homParityShiftAdjunction_unit_app]
  exact comp_mem (homPostUnit_mem (W.adj i h) Z)
    (map_mem (homPost (k := k) (W.F i h)) (homParityShiftSquare_inv_mem _ _))

theorem homContentPostAdjunction_counit_mem (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostAdjunction T W i betaP muP h).counit.app Z ∈
      parity (R := k) _ _ 0 := by
  change ((homPostAdjunction (W.adj i h)).comp
    (homParityShiftAdjunction (homContentShift D i betaP))).counit.app Z ∈ _
  rw [Adjunction.comp_counit_app, homParityShiftAdjunction_counit_app]
  exact comp_mem (map_mem (homParityShift (k := k) (homContentShift D i betaP))
    (homPostCounit_mem (W.adj i h) _)) (homParityShiftSquare_mem _ _)

def homContentPostSuperAdjunction : SuperAdjunction (k := k)
    (homContentPostSuperE T W i betaP muP h) (homContentPostSuperF T W i betaP muP h) :=
  superAdjunctionOfEven (homContentPostAdjunction T W i betaP muP h)
    (homContentPostAdjunction_unit_mem T W i betaP muP h)
    (homContentPostAdjunction_counit_mem T W i betaP muP h)

/-- The even input coordinate, including the sign from the two parity removals. -/
def homContentPostSourceIso (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostE T W i betaP muP h).obj ((homContentPostF T W i betaP muP h).obj Z) ≅
      (Z ≫ W.F i h) ≫ W.E i h :=
  homShiftConjugationIso (homPost (k := k) (W.F i h) ⋙ homPost (k := k) (W.E i h))
    (homContentShift D i betaP) Z

/-- The even output coordinate removes the adjacent parity shifts inside the lowering functor. -/
def homContentPostTargetIso (Z : homWeightSector T W.obj muP muM) :
    (homContentPostF T W i betaP muP h).obj ((homContentPostE T W i betaP muP h).obj Z) ≅
      (Z ≫ W.E i h) ≫ W.F i h :=
  (homPost (k := k) (W.F i h)).mapIso
    ((homParityShiftSquare (k := k) (homContentShift D i betaP)).app (Z ≫ W.E i h))

/-- The specified unit, in its output coordinate. -/
theorem homContentPostAdjunction_unit_coordinates (Z : homWeightSector T W.obj muP muM) :
    (homContentPostAdjunction T W i betaP muP h).unit.app Z =
      (homPostUnit (W.adj i h)).app Z ≫ (homContentPostTargetIso T W i betaP muP h Z).inv := by
  change ((homPostAdjunction (W.adj i h)).comp
    (homParityShiftAdjunction (homContentShift D i betaP))).unit.app Z = _
  rw [Adjunction.comp_unit_app, homParityShiftAdjunction_unit_app]
  rfl

/-- The specified counit, in its input coordinate; the two parity signs cancel. -/
theorem homContentPostAdjunction_counit_coordinates (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostAdjunction T W i betaP muP h).counit.app Z =
      (homContentPostSourceIso T W i betaP muP h Z).hom ≫ (homPostCounit (W.adj i h)).app Z := by
  change ((homPostAdjunction (W.adj i h)).comp
    (homParityShiftAdjunction (homContentShift D i betaP))).counit.app Z = _
  rw [Adjunction.comp_counit_app, homParityShiftAdjunction_counit_app]
  have hc := homShiftConjugationIso_supernatural
    (homPost (k := k) (a := T (-muP)) (W.F i h) ⋙ homPost (k := k) (W.E i h))
    (𝟭 _) (homContentShift D i betaP) 0 (homPostCounit (W.adj i h)).app
    (isSupernatural_of_natTrans (homPostCounit (W.adj i h)) (homPostCounit_mem (W.adj i h))) Z
  rw [homShiftConjugationIso_id] at hc
  exact hc

variable {rhoM : X} (h₂ : nuM + D.α i = rhoM)

/-- The BB word comparison uses beta and xi, followed by the even postcomposition associator. -/
def homContentPostWordIso :
    homContentPostE T W i betaP muP h ⋙ homContentPostE T W i betaP muP h₂ ≅
      homPost (k := k) (a := T (-muP)) (W.E i h ≫ W.E i h₂) :=
  Functor.isoWhiskerLeft (homPost (k := k) (W.E i h))
    (homShiftConjugationNatIso (homPost (k := k) (W.E i h₂)) (homContentShift D i betaP)) ≪≫
    homPostComp (W.E i h) (W.E i h₂)

theorem homContentPostWordIso_hom_app (Z : homWeightSector T W.obj muP muM) :
    (homContentPostWordIso T W i betaP muP h h₂).hom.app Z =
      (homShiftConjugationIso (homPost (k := k) (W.E i h₂))
        (homContentShift D i betaP) (Z ≫ W.E i h)).hom ≫
      (associator Z (W.E i h) (W.E i h₂)).hom := by
  simp [homContentPostWordIso, homShiftConjugationNatIso_hom_app, homPostComp, homPost]

theorem homContentPostWordIso_mem (Z : homWeightSector T W.obj muP muM) :
    (homContentPostWordIso T W i betaP muP h h₂).hom.app Z ∈
      parity (R := k) _ _ 0 := by
  rw [homContentPostWordIso_hom_app]
  exact comp_mem (homShiftConjugationIso_mem (homPost (k := k) (W.E i h₂))
    (homContentShift D i betaP) (Z ≫ W.E i h))
    (TwoSupercategory.associator_hom_mem (R := k) Z (W.E i h) (W.E i h₂))

/-- The prescribed factor crossing, without a scalar gauge change. -/
def homContentPostCrossing :
    homContentPostSuperE T W i betaP muP h ≫ homContentPostSuperE T W i betaP muP h₂ ⟶
      homContentPostSuperE T W i betaP muP h ≫ homContentPostSuperE T W i betaP muP h₂ :=
  ((SuperNatTrans.ofNatTrans (homContentPostWordIso T W i betaP muP h h₂).hom
    (homContentPostWordIso_mem T W i betaP muP h h₂)).vcomp
      (homPostTransform (W.cross i i h h₂ h h₂) (W.loc i h h₂).cross_mem)).vcomp
    (SuperNatTrans.ofNatTrans (homContentPostWordIso T W i betaP muP h h₂).inv
      (fun Z => inv_mem ((homContentPostWordIso T W i betaP muP h h₂).app Z)
        (homContentPostWordIso_mem T W i betaP muP h h₂ Z)))

/-- Both parity components of the specified crossing retain the edge order of the factor. -/
theorem homContentPostCrossing_app (q : ZMod 2)
    (Z : homWeightSector T W.obj muP muM) :
    (homContentPostCrossing T W i betaP muP h h₂).app q Z =
      if q = D.parity i then
        (homContentPostWordIso T W i betaP muP h h₂).hom.app Z ≫
          Z ◁ W.cross i i h h₂ h h₂ ≫
        (homContentPostWordIso T W i betaP muP h h₂).inv.app Z
      else 0 := by
  fin_cases q <;> rcases parity_eq_zero_or_one (D.parity i) with hp | hp <;>
    simp [homContentPostCrossing, SuperNatTrans.ofNatTrans, homPostTransform, hp, Category.assoc]

/-- The two parity comparisons cancel on the specified factor crossing, for all content. -/
theorem homContentPostFactorCrossing_shift (Z : homWeightSector T W.obj muP muM) :
    let p := homContentShift D i betaP
    let F := homPost (k := k) (a := T (-muP)) (W.E i h ≫ W.E i h₂)
    (homParityShift (k := k) p).map
      ((homParityShift (k := k) p).obj Z ◁ W.cross i i h h₂ h h₂) ≫
      (homShiftConjugationIso F p Z).hom =
    (homShiftConjugationIso F p Z).hom ≫ (Z ◁ W.cross i i h h₂ h h₂) := by
  dsimp only
  have ht := (homPostTransform (k := k) (a := T (-muP))
    (W.cross i i h h₂ h h₂) (W.loc i h h₂).cross_mem).isSupernatural (D.parity i)
  have hc := homShiftConjugationIso_supernatural
    (homPost (k := k) (W.E i h ≫ W.E i h₂))
    (homPost (k := k) (W.E i h ≫ W.E i h₂))
    (homContentShift D i betaP) (D.parity i) _ ht Z
  simpa only [homPostTransform, ite_eq_left] using hc

/-- The prescribed BB crossing has the colour parity. -/
theorem homContentPostCrossing_mem : homContentPostCrossing T W i betaP muP h h₂ ∈
    parity (R := k) _ _ (D.parity i) := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.2
  intro q hq
  funext Z
  simp [homContentPostCrossing_app, hq]

end Hom
end OddMath.SKM
