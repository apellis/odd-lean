import OddMath.SKM.RouquierDotSlide

/-!
# Curls for super Rouquier data

This ports the curl calculus of `Categorification/TwoRep/CyclicDotNegOne.lean` (`curlG`),
`BetaCoeffNeg.lean` (`curlEG`), `RouqDottedCurls.lean` (Brundan, *On the definition of
Kac–Moody 2-category*, arXiv:1501.00350v1, Lemma 4.1) and the self-curls of
`RouqTriangleE.lean` to super Rouquier data in a 2-supercategory.

* `curlG u e w` closes the left strand of `w : E₁ E₂ → E₁ E₂` with a cup `u` and a cap `e`
  on the left; `curlEG u e w` closes the right strand on the right.
* Atoms on the closed strand slide into the cup or cap without sign; atoms on the open
  strand leave the curl with the Koszul sign of the cup (bottom) or cap (top) they pass.
* `sig_counit_pitchfork`, `unit_sig_pitchfork`: closing the rightward crossing by a rightward
  cap or cup gives the crossing closed by the other adjunction (no sign: cups and caps are
  even).
* `curlG_dotted` (Brundan (4.2)) and `curlEG_dotted` (Brundan (4.1)). With `s = (-1)^p`, the
  boundary values are `-ε • 1` and `1`, where `ε = 1` if `h = 0` and `ε = s` otherwise for
  (4.2). The extra `s` for `h > 0` comes from the signed dot slide `X σ = s σ Y - s ε η`.
* `curlG_capD_self`, `curlEG_cupD_self`: the boundary curls with all dots on the cap
  (resp. cup) side.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

section Generic

variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}

/-- The curl closing the left strand of `w` on the left. -/
def curlG (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b) (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : E₂ ⟶ E₂ :=
  (leftUnitor E₂).inv ≫ u ▷ E₂ ≫ (associator F₁ E₁ E₂).hom ≫ F₁ ◁ w ≫
    (associator F₁ E₁ E₂).inv ≫ e ▷ E₂ ≫ (leftUnitor E₂).hom

/-- The curl closing the right strand of `w` on the right. -/
def curlEG (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b) (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : E₁ ⟶ E₁ :=
  (rightUnitor E₁).inv ≫ E₁ ◁ u ≫ (associator E₁ E₂ F₂).inv ≫ w ▷ F₂ ≫
    (associator E₁ E₂ F₂).hom ≫ E₁ ◁ e ≫ (rightUnitor E₁).hom

include k in
theorem curlG_add (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b) (w w' : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    curlG u e (w + w') = curlG u e w + curlG u e w' := by
  simp only [curlG, TwoSupercategory.whiskerLeft_add (R := k), Preadditive.comp_add,
    Preadditive.add_comp]

include k in
theorem curlEG_add (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b) (w w' : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    curlEG u e (w + w') = curlEG u e w + curlEG u e w' := by
  simp only [curlEG, TwoSupercategory.add_whiskerRight (R := k), Preadditive.comp_add,
    Preadditive.add_comp]

/-- `curlG u e` as an additive map. -/
def curlGHom (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b) :
    (E₁ ≫ E₂ ⟶ E₁ ≫ E₂) →+ (E₂ ⟶ E₂) :=
  AddMonoidHom.mk' (curlG u e) (curlG_add (k := k) u e)

/-- `curlEG u e` as an additive map. -/
def curlEGHom (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b) :
    (E₁ ≫ E₂ ⟶ E₁ ≫ E₂) →+ (E₁ ⟶ E₁) :=
  AddMonoidHom.mk' (curlEG u e) (curlEG_add (k := k) u e)

theorem curlG_apply (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b) (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    curlGHom (k := k) (E₂ := E₂) u e w = curlG u e w := rfl

theorem curlEG_apply (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b) (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    curlEGHom (k := k) (E₁ := E₁) u e w = curlEG u e w := rfl

include k in
theorem curlG_zsmul (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b) (n : ℤ)
    (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : curlG u e (n • w) = n • curlG u e w := by
  rw [← curlG_apply (k := k), map_zsmul, curlG_apply]

include k in
theorem curlEG_zsmul (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b) (n : ℤ)
    (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : curlEG u e (n • w) = n • curlEG u e w := by
  rw [← curlEG_apply (k := k), map_zsmul, curlEG_apply]

include k in
theorem curlG_neg (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b)
    (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : curlG u e (-w) = -curlG u e w := by
  rw [← curlG_apply (k := k), map_neg, curlG_apply]

include k in
theorem curlEG_neg (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b)
    (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : curlEG u e (-w) = -curlEG u e w := by
  rw [← curlEG_apply (k := k), map_neg, curlEG_apply]

include k in
theorem curlG_sub (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b)
    (w w' : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : curlG u e (w - w') = curlG u e w - curlG u e w' := by
  rw [← curlG_apply (k := k), map_sub, curlG_apply, curlG_apply]

include k in
theorem curlEG_sub (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b)
    (w w' : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : curlEG u e (w - w') = curlEG u e w - curlEG u e w' := by
  rw [← curlEG_apply (k := k), map_sub, curlEG_apply, curlEG_apply]

include k in
theorem curlG_sum {ι : Type*} (s : Finset ι) (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b)
    (w : ι → (E₁ ≫ E₂ ⟶ E₁ ≫ E₂)) :
    curlG u e (∑ i ∈ s, w i) = ∑ i ∈ s, curlG u e (w i) := by
  rw [← curlG_apply (k := k), map_sum]
  rfl

include k in
theorem curlEG_sum {ι : Type*} (s : Finset ι) (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b)
    (w : ι → (E₁ ≫ E₂ ⟶ E₁ ≫ E₂)) :
    curlEG u e (∑ i ∈ s, w i) = ∑ i ∈ s, curlEG u e (w i) := by
  rw [← curlEG_apply (k := k), map_sum]
  rfl

include k in
theorem curlG_zero (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b) :
    curlG (E₂ := E₂) u e 0 = 0 := by
  rw [← curlG_apply (k := k), map_zero]

include k in
theorem curlEG_zero (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b) :
    curlEG (E₁ := E₁) u e 0 = 0 := by
  rw [← curlEG_apply (k := k), map_zero]

include k in
/-- Atoms on the closed strand at the top of `curlG` are absorbed by the cap. -/
theorem curlG_comp_whiskerRight (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b)
    (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (y : E₁ ⟶ E₁) :
    curlG u e (w ≫ y ▷ E₂) = curlG u (F₁ ◁ y ≫ e) w := by
  unfold curlG
  rw [TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

include k in
/-- Atoms on the closed strand at the bottom of `curlG` are absorbed by the cup. -/
theorem curlG_whiskerRight_comp (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b)
    (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (y : E₁ ⟶ E₁) :
    curlG u e (y ▷ E₂ ≫ w) = curlG (u ≫ F₁ ◁ y) e w := by
  unfold curlG
  rw [TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- An atom on the open strand at the bottom of `curlG` leaves past the cup. -/
theorem curlG_whiskerLeft_comp {pu pz : ZMod 2} {u : 𝟙 b ⟶ F₁ ≫ E₁} (hu : u ∈ parity (R := k) _ _ pu)
    (e : F₁ ≫ E₁ ⟶ 𝟙 b) (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) {z : E₂ ⟶ E₂}
    (hz : z ∈ parity (R := k) _ _ pz) :
    curlG u e (E₁ ◁ z ≫ w) = koszulSign pu pz • (z ≫ curlG u e w) := by
  unfold curlG
  have h1 : (associator F₁ E₁ E₂).hom ≫ F₁ ◁ (E₁ ◁ z ≫ w) =
      (F₁ ≫ E₁) ◁ z ≫ (associator F₁ E₁ E₂).hom ≫ F₁ ◁ w := by
    rw [TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.comp_whiskerLeft (R := k)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h2 := TwoSupercategory.super_interchange (R := k) hu hz
  have h3 : (leftUnitor E₂).inv ≫ 𝟙 b ◁ z = z ≫ (leftUnitor E₂).inv := by
    rw [TwoSupercategory.id_whiskerLeft (R := k)]
    simp only [Iso.inv_hom_id_assoc]
  rw [reassoc_of% h1, reassoc_of% h2]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [reassoc_of% h3]

/-- An atom on the open strand at the top of `curlG` leaves past the cap. -/
theorem curlG_comp_whiskerLeft (u : 𝟙 b ⟶ F₁ ≫ E₁) {pe pz : ZMod 2} {e : F₁ ≫ E₁ ⟶ 𝟙 b}
    (he : e ∈ parity (R := k) _ _ pe) (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) {z : E₂ ⟶ E₂}
    (hz : z ∈ parity (R := k) _ _ pz) :
    curlG u e (w ≫ E₁ ◁ z) = koszulSign pe pz • (curlG u e w ≫ z) := by
  unfold curlG
  have h1 : F₁ ◁ (w ≫ E₁ ◁ z) ≫ (associator F₁ E₁ E₂).inv =
      F₁ ◁ w ≫ (associator F₁ E₁ E₂).inv ≫ (F₁ ≫ E₁) ◁ z := by
    rw [TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.comp_whiskerLeft (R := k)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h2 := TwoSupercategory.super_interchange (R := k) he hz
  have h2' : (F₁ ≫ E₁) ◁ z ≫ e ▷ E₂ = koszulSign pe pz • (e ▷ E₂ ≫ 𝟙 b ◁ z) := by
    rw [h2, smul_smul, koszulSign_mul_self, one_smul]
  have h3 : 𝟙 b ◁ z ≫ (leftUnitor E₂).hom = (leftUnitor E₂).hom ≫ z := by
    rw [TwoSupercategory.id_whiskerLeft (R := k)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% h1, reassoc_of% h2']
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [h3]

include k in
/-- The curl of a whiskered atom on the closed strand is a bubble beside the open strand. -/
theorem curlG_whiskerRight (u : 𝟙 b ⟶ F₁ ≫ E₁) (e : F₁ ≫ E₁ ⟶ 𝟙 b) (y : E₁ ⟶ E₁) :
    curlG u e (y ▷ E₂) = (leftUnitor E₂).inv ≫ (u ≫ F₁ ◁ y ≫ e) ▷ E₂ ≫ (leftUnitor E₂).hom := by
  have h := curlG_whiskerRight_comp (k := k) (E₂ := E₂) u e (𝟙 _) y
  rw [Category.comp_id] at h
  rw [h]
  unfold curlG
  rw [TwoSupercategory.whiskerLeft_id (R := k)]
  simp only [Category.id_comp, Iso.hom_inv_id_assoc, TwoSupercategory.comp_whiskerRight (R := k),
    Category.assoc]

include k in
/-- Atoms on the closed strand at the top of `curlEG` are absorbed by the cap. -/
theorem curlEG_comp_whiskerLeft (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b)
    (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (z : E₂ ⟶ E₂) :
    curlEG u e (w ≫ E₁ ◁ z) = curlEG u (z ▷ F₂ ≫ e) w := by
  unfold curlEG
  rw [TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

include k in
/-- Atoms on the closed strand at the bottom of `curlEG` are absorbed by the cup. -/
theorem curlEG_whiskerLeft_comp (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b)
    (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (z : E₂ ⟶ E₂) :
    curlEG u e (E₁ ◁ z ≫ w) = curlEG (u ≫ z ▷ F₂) e w := by
  unfold curlEG
  rw [TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- An atom on the open strand at the bottom of `curlEG` leaves past the cup. -/
theorem curlEG_whiskerRight_comp {pu py : ZMod 2} {u : 𝟙 b ⟶ E₂ ≫ F₂}
    (hu : u ∈ parity (R := k) _ _ pu) (e : E₂ ≫ F₂ ⟶ 𝟙 b) (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    {y : E₁ ⟶ E₁} (hy : y ∈ parity (R := k) _ _ py) :
    curlEG u e (y ▷ E₂ ≫ w) = koszulSign py pu • (y ≫ curlEG u e w) := by
  unfold curlEG
  have h1 : (associator E₁ E₂ F₂).inv ≫ (y ▷ E₂ ≫ w) ▷ F₂ =
      y ▷ (E₂ ≫ F₂) ≫ (associator E₁ E₂ F₂).inv ≫ w ▷ F₂ := by
    rw [TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.whiskerRight_comp (R := k)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h2 := TwoSupercategory.super_interchange (R := k) hy hu
  have h2' : E₁ ◁ u ≫ y ▷ (E₂ ≫ F₂) = koszulSign py pu • (y ▷ 𝟙 b ≫ E₁ ◁ u) := by
    rw [h2, smul_smul, koszulSign_mul_self, one_smul]
  have h3 : (rightUnitor E₁).inv ≫ y ▷ 𝟙 b = y ≫ (rightUnitor E₁).inv := by
    rw [TwoSupercategory.whiskerRight_id (R := k)]
    simp only [Iso.inv_hom_id_assoc]
  rw [reassoc_of% h1, reassoc_of% h2']
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [reassoc_of% h3]

/-- An atom on the open strand at the top of `curlEG` leaves past the cap. -/
theorem curlEG_comp_whiskerRight (u : 𝟙 b ⟶ E₂ ≫ F₂) {pe py : ZMod 2} {e : E₂ ≫ F₂ ⟶ 𝟙 b}
    (he : e ∈ parity (R := k) _ _ pe) (w : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) {y : E₁ ⟶ E₁}
    (hy : y ∈ parity (R := k) _ _ py) :
    curlEG u e (w ≫ y ▷ E₂) = koszulSign py pe • (curlEG u e w ≫ y) := by
  unfold curlEG
  have h1 : (w ≫ y ▷ E₂) ▷ F₂ ≫ (associator E₁ E₂ F₂).hom =
      w ▷ F₂ ≫ (associator E₁ E₂ F₂).hom ≫ y ▷ (E₂ ≫ F₂) := by
    rw [TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.whiskerRight_comp (R := k)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h2 := TwoSupercategory.super_interchange (R := k) hy he
  have h3 : y ▷ 𝟙 b ≫ (rightUnitor E₁).hom = (rightUnitor E₁).hom ≫ y := by
    rw [TwoSupercategory.whiskerRight_id (R := k)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h2' : y ▷ (E₂ ≫ F₂) ≫ E₁ ◁ e = koszulSign py pe • (E₁ ◁ e ≫ y ▷ 𝟙 b) := by
    rw [h2]
  rw [reassoc_of% h1, reassoc_of% h2']
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [h3]

include k in
/-- The curl of a whiskered atom on the closed strand is a bubble beside the open strand. -/
theorem curlEG_whiskerLeft (u : 𝟙 b ⟶ E₂ ≫ F₂) (e : E₂ ≫ F₂ ⟶ 𝟙 b) (z : E₂ ⟶ E₂) :
    curlEG (E₁ := E₁) u e (E₁ ◁ z) =
      (rightUnitor E₁).inv ≫ E₁ ◁ (u ≫ z ▷ F₂ ≫ e) ≫ (rightUnitor E₁).hom := by
  have h := curlEG_whiskerLeft_comp (k := k) (E₁ := E₁) u e (𝟙 _) z
  rw [Category.comp_id] at h
  rw [h]
  unfold curlEG
  rw [TwoSupercategory.id_whiskerRight (R := k)]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc, TwoSupercategory.whiskerLeft_comp (R := k),
    Category.assoc]

/-- A scalar bubble beside a strand. -/
theorem bubble_left_smul_id (E : b ⟶ c) (r : k) :
    (leftUnitor E).inv ≫ (r • 𝟙 (𝟙 b)) ▷ E ≫ (leftUnitor E).hom = r • 𝟙 E := by
  rw [TwoSupercategory.smul_whiskerRight (R := k), TwoSupercategory.id_whiskerRight (R := k)]
  simp

/-- A scalar bubble beside a strand. -/
theorem bubble_right_smul_id (E : a ⟶ b) (r : k) :
    (rightUnitor E).inv ≫ E ◁ (r • 𝟙 (𝟙 b)) ≫ (rightUnitor E).hom = r • 𝟙 E := by
  rw [TwoSupercategory.whiskerLeft_smul (R := k), TwoSupercategory.whiskerLeft_id (R := k)]
  simp

end Generic

/-! ## Even coherence identities

These involve only coherence maps and the (even) units and counits, so they follow from
Mathlib's coherence theorem in the underlying bicategory. -/

section Coherence

open Bicategory in
private theorem gen_counit_close {C : Type*} [Bicategory C] {a b c : C} {E₁ : a ⟶ b}
    {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b} (adj : Bicategory.Adjunction E₂ F₂) :
    ((ρ_ (F₁ ≫ E₁)).inv ≫ (F₁ ≫ E₁) ◁ adj.unit ≫ (α_ F₁ E₁ (E₂ ≫ F₂)).hom ≫
      F₁ ◁ (α_ E₁ E₂ F₂).inv ≫ (α_ F₁ (E₁ ≫ E₂) F₂).inv) ▷ E₂ ≫
      (α_ (F₁ ≫ E₁ ≫ E₂) F₂ E₂).hom ≫ (F₁ ≫ E₁ ≫ E₂) ◁ adj.counit ≫
      (ρ_ (F₁ ≫ E₁ ≫ E₂)).hom = (α_ F₁ E₁ E₂).hom := by
  calc _ = 𝟙 _ ⊗≫ (F₁ ≫ E₁) ◁ leftZigzag adj.unit adj.counit ⊗≫ 𝟙 _ := by
        bicategory
    _ = _ := by rw [adj.left_triangle]; bicategory

open Bicategory in
private theorem gen_unit_close {C : Type*} [Bicategory C] {a b c : C} {E₁ : a ⟶ b}
    {F₁ : b ⟶ a} (Y : b ⟶ c) (adj : Bicategory.Adjunction E₁ F₁) :
    (λ_ (E₁ ≫ Y)).inv ≫ adj.unit ▷ (E₁ ≫ Y) ≫ (α_ E₁ F₁ (E₁ ≫ Y)).hom ≫
      E₁ ◁ ((α_ F₁ E₁ Y).inv ≫ adj.counit ▷ Y ≫ (λ_ Y).hom) = 𝟙 _ := by
  calc _ = 𝟙 _ ⊗≫ leftZigzag adj.unit adj.counit ▷ Y ⊗≫ 𝟙 _ := by
        bicategory
    _ = _ := by rw [adj.left_triangle]; bicategory

open Bicategory in
private theorem gen_prefix {C : Type*} [Bicategory C] {a b c : C} (E : a ⟶ b) (F : b ⟶ a)
    (H : b ⟶ c) (K : c ⟶ b) (η : 𝟙 b ⟶ H ≫ K) :
    (ρ_ (F ≫ E)).inv ≫ (F ≫ E) ◁ η ≫ (α_ F E (H ≫ K)).hom ≫ F ◁ (α_ E H K).inv =
      F ◁ ((ρ_ E).inv ≫ E ◁ η ≫ (α_ E H K).inv) := by
  bicategory

open Bicategory in
private theorem gen_suffix {C : Type*} [Bicategory C] {a b c : C} (E : a ⟶ b) (F : b ⟶ a)
    (H : b ⟶ c) (K : c ⟶ b) (ε : F ≫ E ⟶ 𝟙 b) :
    (α_ F (E ≫ H) K).inv ≫ (α_ F E H).inv ▷ K ≫ (ε ▷ H) ▷ K ≫ (λ_ H).hom ▷ K =
      F ◁ (α_ E H K).hom ≫ (α_ F E (H ≫ K)).inv ≫ ε ▷ (H ≫ K) ≫ (λ_ (H ≫ K)).hom := by
  bicategory

/-- The simp set translating equations in `Underlying2 k B` into equations in `B`. -/
local macro "u2val" h:ident : tactic =>
  `(tactic| (simp only [Underlying.comp_val, Underlying.id_val, Underlying2.comp₂_val,
    Underlying2.id₂_val, Underlying2.whiskerLeft_val, Underlying2.whiskerRight_val,
    Underlying2.associator_hom_val, Underlying2.associator_inv_val,
    Underlying2.leftUnitor_hom_val, Underlying2.leftUnitor_inv_val,
    Underlying2.rightUnitor_hom_val, Underlying2.rightUnitor_inv_val, Underlying2.comp_obj,
    Underlying2.id_obj, Underlying2.hom1_obj] at $h:ident; exact $h:ident))

variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}

theorem counit_close (A₂ : SuperAdjunction (k := k) E₂ F₂) :
    ((rightUnitor (F₁ ≫ E₁)).inv ≫ (F₁ ≫ E₁) ◁ A₂.unit ≫ (associator F₁ E₁ (E₂ ≫ F₂)).hom ≫
      F₁ ◁ (associator E₁ E₂ F₂).inv ≫ (associator F₁ (E₁ ≫ E₂) F₂).inv) ▷ E₂ ≫
      (associator (F₁ ≫ E₁ ≫ E₂) F₂ E₂).hom ≫ (F₁ ≫ E₁ ≫ E₂) ◁ A₂.counit ≫
      (rightUnitor (F₁ ≫ E₁ ≫ E₂)).hom = (associator F₁ E₁ E₂).hom := by
  have h := congrArg Subtype.val (gen_counit_close (E₁ := Underlying2.hom1 (R := k) E₁)
    (F₁ := Underlying2.hom1 (R := k) F₁) A₂.toUnderlying)
  u2val h

theorem unit_close (Y : b ⟶ c) (A₁ : SuperAdjunction (k := k) E₁ F₁) :
    (leftUnitor (E₁ ≫ Y)).inv ≫ A₁.unit ▷ (E₁ ≫ Y) ≫ (associator E₁ F₁ (E₁ ≫ Y)).hom ≫
      E₁ ◁ ((associator F₁ E₁ Y).inv ≫ A₁.counit ▷ Y ≫ (leftUnitor Y).hom) = 𝟙 _ := by
  have h := congrArg Subtype.val (gen_unit_close (Underlying2.hom1 (R := k) Y)
    A₁.toUnderlying)
  u2val h

theorem mate_prefix (A₂ : SuperAdjunction (k := k) E₂ F₂) :
    (rightUnitor (F₁ ≫ E₁)).inv ≫ (F₁ ≫ E₁) ◁ A₂.unit ≫ (associator F₁ E₁ (E₂ ≫ F₂)).hom ≫
      F₁ ◁ (associator E₁ E₂ F₂).inv =
      F₁ ◁ ((rightUnitor E₁).inv ≫ E₁ ◁ A₂.unit ≫ (associator E₁ E₂ F₂).inv) := by
  have h := congrArg Subtype.val (gen_prefix (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₂)
    (Underlying2.hom1 (R := k) F₂) ⟨A₂.unit, A₂.unit_mem⟩)
  u2val h

theorem mate_suffix (A₁ : SuperAdjunction (k := k) E₁ F₁) :
    (associator F₁ (E₁ ≫ E₂) F₂).inv ≫ (associator F₁ E₁ E₂).inv ▷ F₂ ≫
      (A₁.counit ▷ E₂) ▷ F₂ ≫ (leftUnitor E₂).hom ▷ F₂ =
      F₁ ◁ (associator E₁ E₂ F₂).hom ≫ (associator F₁ E₁ (E₂ ≫ F₂)).inv ≫
        A₁.counit ▷ (E₂ ≫ F₂) ≫ (leftUnitor (E₂ ≫ F₂)).hom := by
  have h := congrArg Subtype.val (gen_suffix (Underlying2.hom1 (R := k) E₁)
    (Underlying2.hom1 (R := k) F₁) (Underlying2.hom1 (R := k) E₂)
    (Underlying2.hom1 (R := k) F₂) ⟨A₁.counit, A₁.counit_mem⟩)
  u2val h

end Coherence

/-! ## Pitchforks of the rightward crossing -/

namespace SuperRouquierLoc

variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {p : ZMod 2} {h : ℤ}
  (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)

/-- The rightward crossing with its input cap pulled out. -/
theorem sig_eq_capped :
    L.sig = ((rightUnitor (F₁ ≫ E₁)).inv ≫ (F₁ ≫ E₁) ◁ A₂.unit ≫
      (associator F₁ E₁ (E₂ ≫ F₂)).hom ≫ F₁ ◁ (associator E₁ E₂ F₂).inv ≫
        (associator F₁ (E₁ ≫ E₂) F₂).inv) ≫
      (F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫ A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom) ▷ F₂ := by
  rw [sig, rouquierMate]
  simp only [TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.whisker_assoc (R := k),
    Category.assoc, Iso.inv_hom_id_assoc]

/-- The rightward crossing with its output cup pulled out. -/
theorem sig_eq_cupped :
    L.sig = F₁ ◁ ((rightUnitor E₁).inv ≫ E₁ ◁ A₂.unit ≫ (associator E₁ E₂ F₂).inv ≫
      t ▷ F₂ ≫ (associator E₁ E₂ F₂).hom) ≫ (associator F₁ E₁ (E₂ ≫ F₂)).inv ≫
        A₁.counit ▷ (E₂ ≫ F₂) ≫ (leftUnitor (E₂ ≫ F₂)).hom := by
  rw [sig, rouquierMate, mate_suffix A₁, reassoc_of% (mate_prefix A₂)]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]

/-- Closing the output `F` of the rightward crossing with a rightward cap. -/
theorem sig_counit_pitchfork :
    L.sig ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫ E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom =
      (associator F₁ E₁ E₂).hom ≫ F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫
        A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom := by
  rw [L.sig_eq_capped, TwoSupercategory.comp_whiskerRight (R := k), Category.assoc,
    TwoSupercategory.associator_naturality_left_assoc (R := k),
    TwoSupercategory.whisker_exchange_of_even_right_assoc (R := k) _ A₂.counit_mem,
    TwoSupercategory.rightUnitor_naturality (R := k), reassoc_of% (counit_close A₂)]

/-- Closing the input `E` of the rightward crossing with a rightward cup. -/
theorem unit_sig_pitchfork :
    (leftUnitor E₁).inv ≫ A₁.unit ▷ E₁ ≫ (associator E₁ F₁ E₁).hom ≫ E₁ ◁ L.sig =
      (rightUnitor E₁).inv ≫ E₁ ◁ A₂.unit ≫ (associator E₁ E₂ F₂).inv ≫ t ▷ F₂ ≫
        (associator E₁ E₂ F₂).hom := by
  rw [L.sig_eq_cupped, TwoSupercategory.whiskerLeft_comp (R := k),
    ← TwoSupercategory.associator_naturality_right_assoc (R := k),
    TwoSupercategory.whisker_exchange_of_even_left_assoc (R := k) A₁.unit_mem,
    ← TwoSupercategory.leftUnitor_inv_naturality_assoc (R := k)]
  have hc := unit_close (E₂ ≫ F₂) A₁
  rw [TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.whiskerLeft_comp (R := k)] at hc
  simp only [Category.assoc] at hc ⊢
  rw [TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.whiskerLeft_comp (R := k), hc,
    Category.comp_id]

/-- Closing the output of the rightward crossing gives the curl on `E₂`. -/
theorem close_cup_sig (u : 𝟙 b ⟶ F₁ ≫ E₁) :
    (leftUnitor E₂).inv ≫ (u ≫ L.sig) ▷ E₂ ≫ (associator E₂ F₂ E₂).hom ≫
      E₂ ◁ A₂.counit ≫ (rightUnitor E₂).hom = curlG u A₁.counit t := by
  rw [TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [Category.assoc]
  rw [L.sig_counit_pitchfork]
  rfl

/-- Closing the input of the rightward crossing gives the curl on `E₁`. -/
theorem close_sig_cap (d : E₂ ≫ F₂ ⟶ 𝟙 b) :
    (leftUnitor E₁).inv ≫ A₁.unit ▷ E₁ ≫ (associator E₁ F₁ E₁).hom ≫
      E₁ ◁ (L.sig ≫ d) ≫ (rightUnitor E₁).hom = curlEG A₂.unit d t := by
  rw [TwoSupercategory.whiskerLeft_comp (R := k)]
  simp only [Category.assoc]
  rw [reassoc_of% L.unit_sig_pitchfork]
  simp only [curlEG]

/-! ## Dots through the crossing -/

include L in
/-- Dots below the crossing on the left strand, moved above it. -/
theorem tau_powComp (m : ℕ) :
    t ≫ rouquierPower x₁ m ▷ E₂ = (koszulSign p p ^ m) • (E₁ ◁ rouquierPower x₂ m ≫ t) -
      ∑ j ∈ Finset.range m, (koszulSign p p ^ (j + 1)) •
        (E₁ ◁ rouquierPower x₂ j ≫ rouquierPower x₁ (m - 1 - j) ▷ E₂) := by
  have hY : t ≫ x₁ ▷ E₂ = koszulSign p p • (E₁ ◁ x₂ ≫ t) - koszulSign p p • 𝟙 _ := by
    have hs := L.slide_left
    rw [← hs, smul_sub, smul_smul, koszulSign_mul_self, one_smul]
    abel
  induction m with
  | zero =>
    simp [TwoSupercategory.id_whiskerRight (R := k), TwoSupercategory.whiskerLeft_id (R := k)]
  | succ m ih =>
    rw [rouquierPower_succ, TwoSupercategory.comp_whiskerRight (R := k), ← Category.assoc, ih,
      Preadditive.sub_comp, Preadditive.zsmul_comp, Category.assoc, hY, Preadditive.comp_sub,
      Preadditive.comp_zsmul, Preadditive.comp_zsmul, Category.comp_id, ← Category.assoc,
      ← TwoSupercategory.whiskerLeft_comp (R := k), ← rouquierPower_succ, Preadditive.sum_comp,
      Finset.sum_range_succ, smul_sub, smul_smul, smul_smul, ← pow_succ]
    have hsum : ∑ j ∈ Finset.range m, ((koszulSign p p ^ (j + 1)) •
        (E₁ ◁ rouquierPower x₂ j ≫ rouquierPower x₁ (m - 1 - j) ▷ E₂)) ≫ x₁ ▷ E₂ =
        ∑ j ∈ Finset.range m, (koszulSign p p ^ (j + 1)) •
          (E₁ ◁ rouquierPower x₂ j ≫ rouquierPower x₁ (m + 1 - 1 - j) ▷ E₂) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [Preadditive.zsmul_comp, Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
        ← rouquierPower_succ, show m - 1 - j + 1 = m + 1 - 1 - j by omega]
    rw [hsum, show m + 1 - 1 - m = 0 by omega, rouquierPower_zero,
      TwoSupercategory.id_whiskerRight (R := k), Category.comp_id, pow_succ]
    abel

include L in
/-- Dots below the crossing on the right strand, moved above it. -/
theorem powComp_tau (m : ℕ) :
    E₁ ◁ rouquierPower x₂ m ≫ t = (koszulSign p p ^ m) • (t ≫ rouquierPower x₁ m ▷ E₂) +
      ∑ j ∈ Finset.range m, (koszulSign p p ^ (m - 1 - j)) •
        (E₁ ◁ rouquierPower x₂ j ≫ rouquierPower x₁ (m - 1 - j) ▷ E₂) := by
  have hX : E₁ ◁ x₂ ≫ t = koszulSign p p • (t ≫ x₁ ▷ E₂) + 𝟙 _ := by
    rw [← L.slide_left]
    abel
  induction m with
  | zero =>
    simp [TwoSupercategory.id_whiskerRight (R := k), TwoSupercategory.whiskerLeft_id (R := k)]
  | succ m ih =>
    rw [rouquierPower_succ, TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc, hX,
      Preadditive.comp_add, Preadditive.comp_zsmul, Category.comp_id, ← Category.assoc, ih,
      Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc,
      ← TwoSupercategory.comp_whiskerRight (R := k), ← rouquierPower_succ, Preadditive.sum_comp,
      Finset.sum_range_succ, smul_add, smul_smul, ← pow_succ', Finset.smul_sum]
    have hsum : ∑ j ∈ Finset.range m, koszulSign p p • (((koszulSign p p ^ (m - 1 - j)) •
        (E₁ ◁ rouquierPower x₂ j ≫ rouquierPower x₁ (m - 1 - j) ▷ E₂)) ≫ x₁ ▷ E₂) =
        ∑ j ∈ Finset.range m, (koszulSign p p ^ (m + 1 - 1 - j)) •
          (E₁ ◁ rouquierPower x₂ j ≫ rouquierPower x₁ (m + 1 - 1 - j) ▷ E₂) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [Preadditive.zsmul_comp, Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
        ← rouquierPower_succ, smul_smul, ← pow_succ', show m - 1 - j + 1 = m + 1 - 1 - j by omega]
    rw [hsum, show m + 1 - 1 - m = 0 by omega, rouquierPower_zero,
      TwoSupercategory.id_whiskerRight (R := k), Category.comp_id, pow_zero, one_smul]
    abel

/-! ## Dotted curls (Brundan, Lemma 4.1) -/

/-- The dotted left cup against the rightward crossing, through the boundary degree. -/
theorem cupL_powComp_sig_of_le {n : ℕ} (hn : (n : ℤ) ≤ h) :
    L.cupL ≫ F₁ ◁ rouquierPower x₁ n ≫ L.sig =
      if (n : ℤ) = h then -((if h = 0 then (1 : ℤ) else koszulSign p p) • A₂.unit) else 0 := by
  have hh : 0 ≤ h := by omega
  rcases eq_or_lt_of_le hh with hz | hp
  · have hn0 : n = 0 := by omega
    subst n
    subst h
    rw [rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp,
      L.cupL_sig_expansion]
    simp only [neg_zero, zero_add, Int.toNat_one, Finset.sum_range_one, Nat.cast_zero, zero_sub]
    rw [L.ccw_of_neg_of_eq (by omega) (by omega), Category.id_comp]
    simp [cupD, TwoSupercategory.id_whiskerRight (R := k)]
  · rcases lt_or_eq_of_le hn with hlt | heq
    · rw [L.cupL_powComp_sig hp (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_left heq, ite_eq_right (by omega), L.powComp_sig, Preadditive.comp_sub,
        Preadditive.comp_zsmul, ← Category.assoc, L.cupL_sig hp, Limits.zero_comp, smul_zero,
        zero_sub, Preadditive.comp_sum]
      congr 1
      rw [Finset.sum_eq_single (n - 1)]
      · rw [Preadditive.comp_zsmul, ← Category.assoc, L.cupL_capD hp (by omega), ite_eq_left (by omega),
          Category.id_comp, Nat.sub_self, show n - (n - 1) = 1 by omega, pow_one]
        simp [cupD, TwoSupercategory.id_whiskerRight (R := k)]
      · intro j hj hjn
        have hj' := Finset.mem_range.mp hj
        rw [Preadditive.comp_zsmul, ← Category.assoc, L.cupL_capD hp (by omega), ite_eq_right (by omega),
          Limits.zero_comp, smul_zero]
      · intro hj
        exact False.elim (hj (Finset.mem_range.mpr (by omega)))

/-- **Brundan, Lemma 4.1, (4.2)**, super version: the right curl with at most `h` dots
vanishes below its boundary degree, where it is `-ε • 1` with `ε = 1` if `h = 0` and
`ε = (-1)^p` otherwise. -/
theorem curlG_dotted {n : ℕ} (hn : (n : ℤ) ≤ h) :
    curlG (L.cupL ≫ F₁ ◁ rouquierPower x₁ n) A₁.counit t =
      if (n : ℤ) = h then -((if h = 0 then (1 : ℤ) else koszulSign p p) • 𝟙 E₂) else 0 := by
  rw [← L.close_cup_sig, Category.assoc, L.cupL_powComp_sig_of_le hn]
  by_cases heq : (n : ℤ) = h
  · rw [ite_eq_left heq, ite_eq_left heq]
    generalize (if h = 0 then (1 : ℤ) else koszulSign p p) = c
    rw [TwoSupercategory.neg_whiskerRight (R := k), TwoSupercategory.zsmul_whiskerRight (R := k)]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp]
    rw [A₂.left_triangle]
  · rw [ite_eq_right heq, ite_eq_right heq, TwoSupercategory.zero_whiskerRight (R := k)]
    simp

/-- The rightward crossing against a dotted left cap, through the boundary degree. -/
theorem sig_powComp_capL_of_le {n : ℕ} (hn : (n : ℤ) ≤ -h) :
    L.sig ≫ rouquierPower x₂ n ▷ F₂ ≫ L.capL = if (n : ℤ) = -h then A₁.counit else 0 := by
  have hh : h ≤ 0 := by omega
  have hsig : L.sig ≫ rouquierPower x₂ n ▷ F₂ = (koszulSign p p ^ n) •
      (F₁ ◁ rouquierPower x₁ n ≫ L.sig + ∑ j ∈ Finset.range n,
        (koszulSign p p ^ (n - j)) • (L.capD j ≫ L.cupD (n - 1 - j))) := by
    rw [L.powComp_sig, sub_add_cancel, smul_smul, ← mul_pow, koszulSign_mul_self, one_pow,
      one_smul]
  rcases eq_or_lt_of_le hh with hz | hneg
  · have hn0 : n = 0 := by omega
    subst n
    subst h
    rw [rouquierPower_zero, TwoSupercategory.id_whiskerRight (R := k), Category.id_comp,
      L.sig_capL_expansion, ite_eq_left (by simp)]
    simp only [zero_add, Int.toNat_one, Finset.sum_range_one, Nat.cast_zero]
    rw [L.cw_of_neg_of_eq (by omega) (by omega), Category.comp_id]
    simp [capD, TwoSupercategory.whiskerLeft_id (R := k)]
  · rw [← Category.assoc, hsig, Linear.smul_comp, Preadditive.add_comp, Category.assoc,
      L.sig_capL hneg, Limits.comp_zero, zero_add, Preadditive.sum_comp]
    have hterm : ∀ j ∈ Finset.range n, ((koszulSign p p ^ (n - j)) •
        (L.capD j ≫ L.cupD (n - 1 - j))) ≫ L.capL =
        if (n : ℤ) = -h ∧ j = 0 then (koszulSign p p ^ n) • L.capD 0 else 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [Preadditive.zsmul_comp, Category.assoc, L.cupD_capL hneg (by omega)]
      by_cases hc : (n : ℤ) = -h ∧ j = 0
      · rcases hc with ⟨hc, rfl⟩
        rw [ite_eq_left (by omega), ite_eq_left ⟨hc, rfl⟩, Category.comp_id, Nat.sub_zero]
      · rw [ite_eq_right (by omega), ite_eq_right hc, Limits.comp_zero, smul_zero]
    rw [Finset.sum_congr rfl hterm]
    by_cases hc : (n : ℤ) = -h
    · have hn0 : 0 < n := by omega
      simp only [hc, true_and, ite_true]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr hn0), smul_smul, ← mul_pow,
        koszulSign_mul_self, one_pow, one_smul]
      simp [capD, TwoSupercategory.whiskerLeft_id (R := k)]
    · simp only [hc, false_and, ite_false, Finset.sum_const_zero, smul_zero]

/-- **Brundan, Lemma 4.1, (4.1)**, super version: the left curl with at most `-h` dots
vanishes below its boundary degree, where it is the identity (no sign). -/
theorem curlEG_dotted {n : ℕ} (hn : (n : ℤ) ≤ -h) :
    curlEG A₂.unit (rouquierPower x₂ n ▷ F₂ ≫ L.capL) t =
      if (n : ℤ) = -h then 𝟙 E₁ else 0 := by
  rw [← L.close_sig_cap, L.sig_powComp_capL_of_le hn]
  split_ifs with heq
  · exact A₁.left_triangle
  · rw [TwoSupercategory.whiskerLeft_zero (R := k)]
    simp

/-! ## Boundary self-curls -/

/-- The boundary right curl with all dots on the cap side. -/
theorem curlG_capD_self (hh : 0 ≤ h) :
    curlG L.cupL (L.capD h.toNat) t =
      -((if h = 0 then (1 : ℤ) else koszulSign p p) • 𝟙 E₂) := by
  rcases eq_or_lt_of_le hh with hz | hp
  · subst h
    have := L.curlG_dotted (n := 0) (by omega)
    simpa [capD, TwoSupercategory.whiskerLeft_id (R := k)] using this
  · have hN : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh
    have hb : curlG L.cupL A₁.counit t = 0 := by
      have := L.curlG_dotted (n := 0) (by omega)
      simpa [TwoSupercategory.whiskerLeft_id (R := k), show h ≠ 0 by omega,
        show (0 : ℤ) ≠ h by omega] using this
    rw [ite_eq_right (show h ≠ 0 by omega), capD, ← curlG_comp_whiskerRight (k := k), L.tau_powComp,
      curlG_sub (k := k), curlG_zsmul (k := k), curlG_sum (k := k),
      curlG_whiskerLeft_comp L.cupL_mem _ _ (rouquierPower_mem L.dot₂_mem _), hb,
      Limits.comp_zero, smul_zero, smul_zero, zero_sub]
    congr 1
    have ht : ∀ j ∈ Finset.range h.toNat, curlG L.cupL A₁.counit
        ((koszulSign p p ^ (j + 1)) •
          (E₁ ◁ rouquierPower x₂ j ≫ rouquierPower x₁ (h.toNat - 1 - j) ▷ E₂)) =
        if j = 0 then koszulSign p p • 𝟙 E₂ else 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [curlG_zsmul (k := k),
        curlG_whiskerLeft_comp L.cupL_mem _ _ (rouquierPower_mem L.dot₂_mem _),
        curlG_whiskerRight (k := k)]
      have hc := L.cupL_capD hp (n := h.toNat - 1 - j) (by omega)
      rw [capD] at hc
      rw [hc]
      by_cases hj0 : j = 0
      · subst j
        rw [ite_eq_left (by omega), ite_eq_left rfl, TwoSupercategory.id_whiskerRight (R := k)]
        simp
      · rw [ite_eq_right (by omega), ite_eq_right hj0, TwoSupercategory.zero_whiskerRight (R := k)]
        simp
    rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' _ _, ite_eq_left (Finset.mem_range.mpr (by omega))]

/-- The boundary left curl with all dots on the cup side (no sign). -/
theorem curlEG_cupD_self (hh : h ≤ 0) :
    curlEG (L.cupD (-h).toNat) L.capL t = 𝟙 E₁ := by
  rcases lt_or_eq_of_le hh with hn | hz
  · have hb : curlEG A₂.unit L.capL t = 0 := by
      have := L.curlEG_dotted (n := 0) (by omega)
      simpa [TwoSupercategory.id_whiskerRight (R := k), show h ≠ 0 by omega] using this
    rw [cupD, ← curlEG_whiskerLeft_comp (k := k), L.powComp_tau, curlEG_add (k := k),
      curlEG_zsmul (k := k), curlEG_comp_whiskerRight _ L.capL_mem _ (rouquierPower_mem L.dot₁_mem _),
      hb, Limits.zero_comp, smul_zero, smul_zero, zero_add, curlEG_sum (k := k)]
    have ht : ∀ j ∈ Finset.range (-h).toNat, curlEG A₂.unit L.capL
        ((koszulSign p p ^ ((-h).toNat - 1 - j)) •
          (E₁ ◁ rouquierPower x₂ j ≫ rouquierPower x₁ ((-h).toNat - 1 - j) ▷ E₂)) =
        if j = (-h).toNat - 1 then 𝟙 E₁ else 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [curlEG_zsmul (k := k), curlEG_whiskerLeft_comp (k := k),
        show A₂.unit ≫ rouquierPower x₂ j ▷ F₂ = L.cupD j from rfl]
      rw [show rouquierPower x₁ ((-h).toNat - 1 - j) ▷ E₂ =
          rouquierPower x₁ ((-h).toNat - 1 - j) ▷ E₂ ≫ 𝟙 _ from (Category.comp_id _).symm,
        curlEG_whiskerRight_comp (L.cupD_mem j) _ _ (rouquierPower_mem L.dot₁_mem _)]
      have hc : curlEG (E₁ := E₁) (L.cupD j) L.capL (𝟙 _) =
          (rightUnitor E₁).inv ≫ E₁ ◁ (L.cupD j ≫ L.capL) ≫ (rightUnitor E₁).hom := by
        have := curlEG_whiskerLeft (k := k) (E₁ := E₁) (L.cupD j) L.capL (𝟙 _)
        rw [TwoSupercategory.whiskerLeft_id (R := k), TwoSupercategory.id_whiskerRight (R := k),
          Category.id_comp] at this
        exact this
      rw [hc, L.cupD_capL hn (by omega)]
      by_cases hj0 : j = (-h).toNat - 1
      · subst j
        rw [ite_eq_left (by omega), ite_eq_left rfl, TwoSupercategory.whiskerLeft_id (R := k)]
        simp
      · rw [ite_eq_right (by omega), ite_eq_right hj0, TwoSupercategory.whiskerLeft_zero (R := k)]
        simp
    rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq' _ _, ite_eq_left (Finset.mem_range.mpr (by omega))]
  · subst h
    have := L.curlEG_dotted (n := 0) (by omega)
    simpa [cupD, TwoSupercategory.id_whiskerRight (R := k)] using this

end SuperRouquierLoc

end OddMath.SKM
