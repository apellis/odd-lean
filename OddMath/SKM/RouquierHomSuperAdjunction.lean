import OddMath.SKM.RouquierNormalizedHomAdjunction
import StringDiagrams.Super.SCat

/-!
# Normalized Hom adjunctions in the supercategory of supercategories

The normalized Hom adjunction is packaged in the existing `SCat` interface.
The component formula for `rouquierMate` supplies the unit–crossing–counit
word of `HomPrincipalMate.md`, §2. No principal-block comparison is asserted.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section SCat
variable {k : Type r} [CommRing k] {A B C : SCat.{r, v, u} k}

/-- An ordinary adjunction with even components defines an adjunction in `SCat`. -/
def superAdjunctionOfEven {E : A ⟶ B} {F : B ⟶ A}
    (adj : E.toFunctor ⊣ F.toFunctor)
    (hu : ∀ Z, adj.unit.app Z ∈ parity (R := k) _ _ 0)
    (hc : ∀ Z, adj.counit.app Z ∈ parity (R := k) _ _ 0) :
    SuperAdjunction (k := k) E F where
  unit := SuperNatTrans.ofNatTrans adj.unit hu
  counit := SuperNatTrans.ofNatTrans adj.counit hc
  unit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  counit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  left_triangle := by
    simp only [SCat.leftUnitor_inv, SCat.associator_hom, SCat.rightUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro Z
      simp [SuperNatTrans.ofNatTrans, Superfunctor.map, Superfunctor.obj]
    · intro Z
      simp [SuperNatTrans.ofNatTrans]
  right_triangle := by
    simp only [SCat.rightUnitor_inv, SCat.associator_inv, SCat.leftUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro Z
      simp [SuperNatTrans.ofNatTrans, Superfunctor.map, Superfunctor.obj]
    · intro Z
      simp [SuperNatTrans.ofNatTrans]

/-- Literal component formula for the defined mate. The crossing may have either parity. -/
theorem rouquierMate_scat_app {E₁ : A ⟶ B} {F₁ : B ⟶ A}
    {E₂ : B ⟶ C} {F₂ : C ⟶ B}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (p : ZMod 2) (Z : B.carrier) :
    (rouquierMate A₁ A₂ t).app p Z =
      A₂.unit.app 0 (E₁.obj (F₁.obj Z)) ≫
        F₂.map (t.app p (F₁.obj Z)) ≫ F₂.map (E₂.map (A₁.counit.app 0 Z)) := by
  have hu := Superfunctor.app_eq_zero_of_mem A₂.unit_mem (by decide : (1 : ZMod 2) ≠ 0)
  have hc := Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide : (1 : ZMod 2) ≠ 0)
  fin_cases p <;>
    simp [rouquierMate, SCat.whiskerLeft_def, SCat.whiskerRight_def,
      Superfunctor.whiskerLeft_app, Superfunctor.whiskerRight_app, hu, hc]
end SCat

section Hom
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP : X} (h : -nuP + D.α i = -muP)

/-- Raising precomposition, bundled as a superfunctor. -/
def homContentSuperE : SCat.of k (homWeightSector T.obj W muP muM) ⟶
    SCat.of k (homWeightSector T.obj W nuP muM) :=
  ⟨homPre (k := k) (T.E i h)⟩

/-- The output-shifted lowering precomposition, bundled as a superfunctor. -/
def homContentSuperF : SCat.of k (homWeightSector T.obj W nuP muM) ⟶
    SCat.of k (homWeightSector T.obj W muP muM) :=
  ⟨homPre (k := k) (T.F i h) ⋙ homParityShift (k := k) (leftAdjParity D i (-nuP))⟩

/-- The specified normalized unit is even after its output comparison. -/
theorem homContentPreAdjunction_unit_mem (Z : homWeightSector T.obj W muP muM) :
    (homContentPreAdjunction T W T.leftAdjoints i muM h).unit.app Z ∈
      parity (R := k) _ _ 0 := by
  rw [homContentPreAdjunction_leftAdjoints_unit_app]
  have hh := comp_mem (comp_mem (comp_mem
    (inv_mem (leftUnitor Z) (TwoSupercategory.leftUnitor_hom_mem (R := k) Z))
    (TwoSupercategory.whiskerRight_mem Z (T.leftCup_mem i h)))
    (TwoSupercategory.associator_hom_mem (R := k) _ _ _))
    ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).inv_mem _)
  simpa only [homContentPreE, homContentPreF, homPre, Functor.comp_obj, Functor.id_obj,
    zero_add, add_zero, zmod2_add_self, Category.assoc] using hh

/-- The specified inverse-scaled counit is even after its input comparison. -/
theorem homContentPreAdjunction_counit_mem (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z ∈
      parity (R := k) _ _ 0 := by
  rw [homContentPreAdjunction_leftAdjoints_counit_app]
  apply zsmul_mem
  have hh := comp_mem (comp_mem (comp_mem
    (TwoSupercategory.whiskerLeft_mem (T.E i h)
      ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).hom_mem _))
    (inv_mem (associator (T.E i h) (T.F i h) Z)
      (TwoSupercategory.associator_hom_mem (R := k) _ _ _)))
    (TwoSupercategory.whiskerRight_mem Z
      (Submodule.smul_mem _ ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k)) (T.leftCap_mem i h))))
    (TwoSupercategory.leftUnitor_hom_mem (R := k) Z)
  simpa only [homContentPreE, homContentPreF, homPre, Functor.comp_obj, Functor.id_obj,
    add_zero, zmod2_add_self, Category.assoc] using hh

/-- The normalized Hom adjunction in the existing `SCat` 2-supercategory. -/
def homContentSuperAdjunction : SuperAdjunction (k := k)
    (homContentSuperE T W i muM h) (homContentSuperF T W i muM h) :=
  superAdjunctionOfEven (homContentPreAdjunction T W T.leftAdjoints i muM h)
    (homContentPreAdjunction_unit_mem T W i muM h)
    (homContentPreAdjunction_counit_mem T W i muM h)

/-- The mate on the normalized Hom sectors is the literal unit–map–map word.
This applies to every component, in particular to either homogeneous crossing parity. -/
theorem homContentSuperAdjunction_mate_app {rhoP : X}
    (h₂ : -rhoP + D.α i = -nuP)
    (t : homContentSuperE T W i muM h ≫ homContentSuperE T W i muM h₂ ⟶
      homContentSuperE T W i muM h ≫ homContentSuperE T W i muM h₂)
    (p : ZMod 2) (Z : homWeightSector T.obj W nuP muM) :
    (rouquierMate (homContentSuperAdjunction T W i muM h)
      (homContentSuperAdjunction T W i muM h₂) t).app p Z =
      (homContentPreAdjunction T W T.leftAdjoints i muM h₂).unit.app
        ((homContentPreE T W i muM h).obj ((homContentPreF T W i muM h).obj Z)) ≫
      (homContentPreF T W i muM h₂).map
        (t.app p ((homContentPreF T W i muM h).obj Z)) ≫
      (homContentPreF T W i muM h₂).map ((homContentPreE T W i muM h₂).map
        ((homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z)) := by
  exact rouquierMate_scat_app _ _ t p Z

end Hom
end OddMath.SKM
