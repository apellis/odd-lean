import OddMath.SKM.RouquierHomPrincipal
import OddMath.SKM.RouquierHomReservoirPowers
import OddMath.SKM.RouquierLeftWindowInverse

/-!
# Coordinates of the normalized precomposition windows

The source and target coordinates in `SwappedHomInversion.md`, §2 include
both the homogeneous shift removal and the even associator. The forward
entries below are the prescribed mate and dotted normalized unit, not maps
defined by conjugating the raw inverse. The alpha and gamma signs are retained,
including gamma(0) = (-1)^p.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

private theorem preIso_factor {C : Type*} [Category C] [Preadditive C]
    {A B X Y U V : C} (a : A ≅ X) (b : B ≅ Y) (c : X ≅ U) (d : Y ≅ V)
    (f : A ⟶ B) (r : U ⟶ V) (s : ℤ)
    (ht : a.inv ≫ f ≫ b.hom = s • (c.hom ≫ r ≫ d.inv)) :
    f = s • ((a ≪≫ c).hom ≫ r ≫ (b ≪≫ d).inv) := by
  apply (cancel_mono b.hom).mp
  apply (cancel_epi a.inv).mp
  simpa only [Iso.trans_hom, Iso.trans_inv, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using ht

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP rhoP : X}
  (h : -nuP + D.α i = -muP) (h₂ : -rhoP + D.α i = -nuP)

/-- Source shift removal followed by reassociation to the factor mixed word. -/
def homContentPreInverseSource (Z : homWeightSector T.obj W nuP muM) :=
  (homPre (k := k) (T.E i h)).mapIso
    ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso (T.F i h ≫ Z)) ≪≫
      (associator (T.E i h) (T.F i h) Z).symm

/-- Target shift removal followed by the corresponding even reassociation. -/
def homContentPreInverseTarget (Z : homWeightSector T.obj W nuP muM) :=
  ((homParityShiftDatum (k := k) (leftAdjParity D i (-rhoP))).iso
    (T.F i h₂ ≫ T.E i h₂ ≫ Z)) ≪≫
      (associator (T.F i h₂) (T.E i h₂) Z).symm

theorem homContentPreInverseSource_mem (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreInverseSource T W i muM h Z).hom ∈
      parity (R := k) _ _ (leftAdjParity D i (-nuP)) := by
  simpa only [homContentPreInverseSource, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, add_zero] using
    comp_mem (map_mem (homPre (k := k) (T.E i h))
      ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).hom_mem (T.F i h ≫ Z)))
      (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) (T.E i h) (T.F i h) Z))

theorem homContentPreInverseTarget_mem (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreInverseTarget T W i muM h₂ Z).hom ∈
      parity (R := k) _ _ (leftAdjParity D i (-nuP)) := by
  have he := leftAdjParity_edge D i h₂
  simpa only [homContentPreInverseTarget, Iso.trans_hom, Iso.symm_hom, add_zero, he] using
    comp_mem ((homParityShiftDatum (k := k) (leftAdjParity D i (-rhoP))).hom_mem
      (T.F i h₂ ≫ T.E i h₂ ≫ Z))
      (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) (T.F i h₂) (T.E i h₂) Z))

/-- The height-dependent principal coefficient, including its empty-window value. -/
def homPreGamma (p : ZMod 2) (a : ℤ) : ℤ :=
  if a = 0 then koszulSign p p else koszulSign p (p * (a : ZMod 2))

theorem homPreGamma_mul_self (p : ZMod 2) (a : ℤ) :
    homPreGamma p a * homPreGamma p a = 1 := by
  unfold homPreGamma
  split_ifs <;> exact koszulSign_mul_self _ _

/-- The cap normalization in the precomposition window, including the
source-height adjunction scalar. -/
def homPreBeta (p σ : ZMod 2) (a : ℤ) (n : ℕ) : ℤ :=
  koszulSign σ (1 + (n : ZMod 2) * p) *
    (koszulSign σ σ * (if a < 0 then 1 else koszulSign p p))

theorem homPreBeta_mul_self (p σ : ZMod 2) (a : ℤ) (n : ℕ) :
    homPreBeta p σ a n * homPreBeta p σ a n = 1 := by
  unfold homPreBeta
  have h : (if a < 0 then 1 else koszulSign p p) *
      (if a < 0 then 1 else koszulSign p p) = 1 := by
    split_ifs <;> simp only [one_mul, koszulSign_mul_self]
  calc
    _ = (koszulSign σ (1 + (n : ZMod 2) * p) *
        koszulSign σ (1 + (n : ZMod 2) * p)) *
        (koszulSign σ σ * koszulSign σ σ) *
        ((if a < 0 then 1 else koszulSign p p) *
          (if a < 0 then 1 else koszulSign p p)) := by ring
    _ = 1 := by rw [koszulSign_mul_self, koszulSign_mul_self, h]; ring

/-- The literal cup–crossing–cap mate of the specified normalized pre adjunctions. -/
def homContentPreMate (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreE T W i muM h).obj ((homContentPreF T W i muM h).obj Z) ⟶
      (homContentPreF T W i muM h₂).obj ((homContentPreE T W i muM h₂).obj Z) :=
  (rouquierMate (homContentSuperAdjunction T W i muM h)
    (homContentSuperAdjunction T W i muM h₂)
    (homContentCrossing T W i muM h h₂)).app (D.parity i) Z

theorem homContentPreMate_coordinates (Z : homWeightSector T.obj W nuP muM) :
    homContentPreMate T W i muM h h₂ Z =
      homPreGamma (D.parity i) (D.h i (-nuP)) •
        ((homContentPreInverseSource T W i muM h Z).hom ≫
          (-(T.loc i h₂ h).sigL) ▷ Z ≫
          (homContentPreInverseTarget T W i muM h₂ Z).inv) := by
  exact preIso_factor
    ((homPre (k := k) (T.E i h)).mapIso
      ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso (T.F i h ≫ Z)))
    ((homParityShiftDatum (k := k) (leftAdjParity D i (-rhoP))).iso
      (T.F i h₂ ≫ T.E i h₂ ≫ Z))
    (associator (T.E i h) (T.F i h) Z).symm
    (associator (T.F i h₂) (T.E i h₂) Z).symm
    _ _ _ (homContentCrossing_principal T W i muM h h₂ Z)

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem pre_leftCup_loc {x y z : X}
    (e₁ : x + D.α i = y) (e₂ : y + D.α i = z) :
    T.leftCup i e₁ = (T.loc i e₁ e₂).cupL := by
  subst z
  rfl

/-- Every prescribed dotted unit has the alpha coefficient in factor coordinates. -/
theorem homReservoirCup_factor (n : ℕ) (Z : homWeightSector T.obj W nuP muM) :
    homReservoirCup T W i muM h₂ n Z =
      koszulSign (leftAdjParity D i (-nuP)) (n * D.parity i) •
        ((leftUnitor Z).inv ≫ (T.loc i h₂ h).leftWindowCup n ▷ Z ≫
          (homContentPreInverseTarget T W i muM h₂ Z).inv) := by
  apply (cancel_mono ((homParityShiftDatum (k := k) (leftAdjParity D i (-rhoP))).iso
    (T.F i h₂ ≫ T.E i h₂ ≫ Z)).hom).mp
  rw [homReservoirCup_coordinates]
  rw [leftAdjParity_edge D i h₂]
  simp only [homContentPreInverseTarget, Iso.trans_inv, Iso.symm_inv,
    Preadditive.zsmul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    SuperRouquierLoc.leftWindowCup, TwoSupercategory.comp_whiskerRight (R := k)]
  rw [pre_leftCup_loc T i h₂ h]
  rw [TwoSupercategory.associator_naturality_middle (R := k)]

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem pre_leftCap_loc {x y z : X}
    (e₁ : x + D.α i = y) (e₂ : y + D.α i = z) :
    T.leftCap i e₂ = (T.loc i e₁ e₂).capL := by
  have hx : x = y - D.α i := eq_sub_of_add_eq e₁
  subst x
  rfl

/-- The prescribed dotted normalized counit is the cap-window entry in
actual source coordinates; beta retains the source-height scalar. -/
theorem homReservoirCap_factor (n : ℕ) (Z : homWeightSector T.obj W nuP muM) :
    homReservoirCap T W i muM h n Z =
      homPreBeta (D.parity i) (leftAdjParity D i (-nuP)) (D.h i (-nuP)) n •
        ((homContentPreInverseSource T W i muM h Z).hom ≫
          (T.loc i h₂ h).leftWindowCap n ▷ Z ≫ (leftUnitor Z).hom) := by
  rw [homReservoirCap_coordinates, T.leftAdjScalar_inv_coe]
  rw [TwoSupercategory.smul_whiskerRight (R := k)]
  simp only [homContentPreInverseSource, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, homPre, SuperRouquierLoc.leftWindowCap,
    TwoSupercategory.comp_whiskerRight (R := k), pre_leftCap_loc T i h₂ h,
    Linear.comp_smul, Linear.smul_comp, homPreBeta, Category.assoc]
  rw [TwoSupercategory.associator_inv_naturality_left_assoc (R := k)]
  simp only [Int.cast_smul_eq_zsmul, smul_smul]

end OddMath.SKM
