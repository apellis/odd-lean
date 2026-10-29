/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.PureBlock
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.MixedInterchangePostPair

/-! # The braid relation on the reservoir path `RRR` of `Eᵢ Eᵢ Eᵢ`

For the relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, at `Eᵢ Eᵢ Eᵢ`, the path `RRR` with three reservoir summands is the only path to
its endpoint. On it the left and right crossings of the swapped generators are the reservoir
crossings `postCrossSame`: factor crossings of `W`, transported by the comparisons `Θ` which
remove the content shifts `Πσ`.

Both crossings are carried, by the parity-`σ` comparisons of the three shifts, to the factor
crossings acting on `((Z F₁) F₂) F₃`, and both pick up the same sign `(-1)^(σ p)`, where `p` is
the parity of the crossing: the left crossing through the super interchange law, the right
crossing through the signed naturality of the outer shift. The braid relation on `RRR` is then
the factor braid relation `W.braid`, whiskered on the left (`post_whisker_braid`).

## Main results

* `post_whisker_braid`: the braid relation of `x ⊗ 1` and `1 ⊗ y` on `F₁ F₂ F₃` survives
  whiskering on the left.
* `shifted_post_braid`: the braid relation for crossings transported by `Θ`.
* `ProbeReservoir.postCrossSame_braid`: the braid relation for the reservoir crossings.
* `ProbeReservoir.rrr_braid`: (1.9) on the path `RRR` of the colour pattern `iii`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams BicategoryStruct Supercategory

/-- Two endomorphisms intertwined by a monomorphism with endomorphisms satisfying the braid
relation satisfy it as well. -/
theorem braid_of_intertwine {C : Type*} [Category C] {X Y : C} (g : X ⟶ Y) [Mono g]
    {L R : X ⟶ X} {A B : Y ⟶ Y} (hL : L ≫ g = g ≫ A) (hR : R ≫ g = g ≫ B)
    (h : A ≫ B ≫ A = B ≫ A ≫ B) : L ≫ R ≫ L = R ≫ L ≫ R := by
  rw [← cancel_mono g]
  simp only [Category.assoc, hL, hR, reassoc_of% hL, reassoc_of% hR, h]

section Whisker

/-- Right whiskering of an isomorphism. -/
def whiskerRightIso (R : Type*) [CommRing R] {C : Type*} [BicategoryStruct C]
    [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
    [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C] {a b c : C} {f g : a ⟶ b}
    (e : f ≅ g) (h : b ⟶ c) : f ≫ h ≅ g ≫ h where
  hom := e.hom ▷ h
  inv := e.inv ▷ h
  hom_inv_id := TwoSupercategory.hom_inv_whiskerRight (R := R) e h
  inv_hom_id := TwoSupercategory.inv_hom_whiskerRight (R := R) e h

/-- A braid relation between `x ⊗ 1` and `1 ⊗ y` on `F₁ F₂ F₃` survives whiskering on the
left by `Z`, with the crossings reassociated to act on `((Z F₁) F₂) F₃`. -/
theorem post_whisker_braid (R : Type*) [CommRing R] {C : Type*} [BicategoryStruct C]
    [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
    [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C] {a b c d e : C}
    (Z : a ⟶ b) {F₁ : b ⟶ c} {F₂ : c ⟶ d} {F₃ : d ⟶ e}
    (x : F₁ ≫ F₂ ⟶ F₁ ≫ F₂) (y : F₂ ≫ F₃ ⟶ F₂ ≫ F₃)
    (hb : F₁ ◁ y ≫ ((associator F₁ F₂ F₃).inv ≫ x ▷ F₃ ≫ (associator F₁ F₂ F₃).hom) ≫
        F₁ ◁ y =
      ((associator F₁ F₂ F₃).inv ≫ x ▷ F₃ ≫ (associator F₁ F₂ F₃).hom) ≫ F₁ ◁ y ≫
        ((associator F₁ F₂ F₃).inv ≫ x ▷ F₃ ≫ (associator F₁ F₂ F₃).hom)) :
    ((associator (Z ≫ F₁) F₂ F₃).hom ≫ (Z ≫ F₁) ◁ y ≫ (associator (Z ≫ F₁) F₂ F₃).inv) ≫
        ((associator Z F₁ F₂).hom ≫ Z ◁ x ≫ (associator Z F₁ F₂).inv) ▷ F₃ ≫
        ((associator (Z ≫ F₁) F₂ F₃).hom ≫ (Z ≫ F₁) ◁ y ≫ (associator (Z ≫ F₁) F₂ F₃).inv) =
      ((associator Z F₁ F₂).hom ≫ Z ◁ x ≫ (associator Z F₁ F₂).inv) ▷ F₃ ≫
        ((associator (Z ≫ F₁) F₂ F₃).hom ≫ (Z ≫ F₁) ◁ y ≫ (associator (Z ≫ F₁) F₂ F₃).inv) ≫
        ((associator Z F₁ F₂).hom ≫ Z ◁ x ≫ (associator Z F₁ F₂).inv) ▷ F₃ := by
  set t := (associator F₁ F₂ F₃).inv ≫ x ▷ F₃ ≫ (associator F₁ F₂ F₃).hom with ht
  have hpent := TwoSupercategory.pentagon (R := R) Z F₁ F₂ F₃
  refine braid_of_intertwine
    ((associator (Z ≫ F₁) F₂ F₃).hom ≫ (associator Z F₁ (F₂ ≫ F₃)).hom)
    (A := Z ◁ (F₁ ◁ y)) (B := Z ◁ t) ?_ ?_ ?_
  · simp only [Category.assoc, Iso.inv_hom_id_assoc,
      TwoSupercategory.associator_naturality_right (R := R)]
  · rw [← hpent]
    simp only [Category.assoc, TwoSupercategory.comp_whiskerRight (R := R),
      TwoSupercategory.inv_hom_whiskerRight_assoc (R := R),
      TwoSupercategory.associator_naturality_middle_assoc (R := R), ht,
      TwoSupercategory.whiskerLeft_comp (R := R),
      TwoSupercategory.whiskerLeft_hom_inv_assoc (R := R)]
  · simp only [← TwoSupercategory.whiskerLeft_comp (R := R), hb]

end Whisker

universe u v w r

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d e f : B}

/-- `Θ_σ(Y)` is, up to the sign `(-1)^σ`, the two parity-`σ` comparisons followed by the
associator. -/
theorem homShiftPairIso_hom_signed (F₁ : c ⟶ d) (F₂ : d ⟶ e) (σ : ZMod 2) (Y : a ⟶ c) :
    (homShiftPairIso (k := k) F₁ F₂ σ Y).hom =
      sign k (σ * σ) •
        (((homParityShiftDatum (k := k) σ).iso
            ((homParityShift (k := k) σ).obj (Y ≫ F₁) ≫ F₂)).hom ≫
          ((homParityShiftDatum (k := k) σ).iso (Y ≫ F₁)).hom ▷ F₂ ≫
          (associator Y F₁ F₂).hom) := by
  rw [homShiftPairIso_hom, reassoc_of% ((homParityShiftDatum (k := k) σ).hom_naturality
    (TwoSupercategory.whiskerRight_mem F₂ ((homParityShiftDatum (k := k) σ).hom_mem _))),
    Linear.smul_comp, Category.assoc]

/-- `Θ_σ(Y)` is even. -/
theorem homShiftPairIso_hom_mem (F₁ : c ⟶ d) (F₂ : d ⟶ e) (σ : ZMod 2) (Y : a ⟶ c) :
    (homShiftPairIso (k := k) F₁ F₂ σ Y).hom ∈ parity (R := k) _ _ 0 := by
  rw [homShiftPairIso, Iso.trans_hom]
  have h := comp_mem (homShiftConjugationIso_mem (homPost (k := k) F₂) σ (Y ≫ F₁))
    (TwoSupercategory.associator_hom_mem (R := k) Y F₁ F₂)
  rw [add_zero] at h
  exact h

/-- **The braid relation for crossings transported by `Θ`.** For parity-`p` crossings `x` on
`F₁ F₂` and `y` on `F₂ F₃` satisfying the braid relation, the crossing `y` transported by
`Θ_σ(Πσ(Z F₁))` and the shift of the crossing `x` transported by `Θ_σ(Z)` satisfy the braid
relation on `Πσ(Πσ(Πσ(Z F₁) F₂) F₃)`. Both are carried to the factor crossings on
`((Z F₁) F₂) F₃` with the same sign `(-1)^(σ p)`. -/
theorem shifted_post_braid (σ p : ZMod 2) (Z : a ⟶ b) {F₁ : b ⟶ c} {F₂ : c ⟶ d}
    {F₃ : d ⟶ e} (x : F₁ ≫ F₂ ⟶ F₁ ≫ F₂) (y : F₂ ≫ F₃ ⟶ F₂ ≫ F₃)
    (hx : x ∈ parity (R := k) _ _ p) (hy : y ∈ parity (R := k) _ _ p)
    (hb : F₁ ◁ y ≫ ((associator F₁ F₂ F₃).inv ≫ x ▷ F₃ ≫ (associator F₁ F₂ F₃).hom) ≫
        F₁ ◁ y =
      ((associator F₁ F₂ F₃).inv ≫ x ▷ F₃ ≫ (associator F₁ F₂ F₃).hom) ≫ F₁ ◁ y ≫
        ((associator F₁ F₂ F₃).inv ≫ x ▷ F₃ ≫ (associator F₁ F₂ F₃).hom)) :
    ((homShiftPairIso (k := k) F₂ F₃ σ ((homParityShift (k := k) σ).obj (Z ≫ F₁))).hom ≫
        (homParityShift (k := k) σ).obj (Z ≫ F₁) ◁ y ≫
        (homShiftPairIso (k := k) F₂ F₃ σ ((homParityShift (k := k) σ).obj (Z ≫ F₁))).inv) ≫
      (homParityShift (k := k) σ).map (((homShiftPairIso (k := k) F₁ F₂ σ Z).hom ≫ Z ◁ x ≫
        (homShiftPairIso (k := k) F₁ F₂ σ Z).inv) ▷ F₃) ≫
      ((homShiftPairIso (k := k) F₂ F₃ σ ((homParityShift (k := k) σ).obj (Z ≫ F₁))).hom ≫
        (homParityShift (k := k) σ).obj (Z ≫ F₁) ◁ y ≫
        (homShiftPairIso (k := k) F₂ F₃ σ ((homParityShift (k := k) σ).obj (Z ≫ F₁))).inv) =
    (homParityShift (k := k) σ).map (((homShiftPairIso (k := k) F₁ F₂ σ Z).hom ≫ Z ◁ x ≫
        (homShiftPairIso (k := k) F₁ F₂ σ Z).inv) ▷ F₃) ≫
      ((homShiftPairIso (k := k) F₂ F₃ σ ((homParityShift (k := k) σ).obj (Z ≫ F₁))).hom ≫
        (homParityShift (k := k) σ).obj (Z ≫ F₁) ◁ y ≫
        (homShiftPairIso (k := k) F₂ F₃ σ ((homParityShift (k := k) σ).obj (Z ≫ F₁))).inv) ≫
      (homParityShift (k := k) σ).map (((homShiftPairIso (k := k) F₁ F₂ σ Z).hom ≫ Z ◁ x ≫
        (homShiftPairIso (k := k) F₁ F₂ σ Z).inv) ▷ F₃) := by
  set Θ₁ := homShiftPairIso (k := k) F₂ F₃ σ ((homParityShift (k := k) σ).obj (Z ≫ F₁))
    with hΘ₁def
  set Θ₂ := homShiftPairIso (k := k) F₁ F₂ σ Z with hΘ₂def
  let ξ₀ := (homParityShiftDatum (k := k) σ).iso
    ((homParityShift (k := k) σ).obj ((homParityShift (k := k) σ).obj (Z ≫ F₁) ≫ F₂) ≫ F₃)
  let ξ₁ := (homParityShiftDatum (k := k) σ).iso
    ((homParityShift (k := k) σ).obj (Z ≫ F₁) ≫ F₂)
  let ξ₂ := (homParityShiftDatum (k := k) σ).iso (Z ≫ F₁)
  let G : (homParityShift (k := k) σ).obj ((homParityShift (k := k) σ).obj
      ((homParityShift (k := k) σ).obj (Z ≫ F₁) ≫ F₂) ≫ F₃) ≅ ((Z ≫ F₁) ≫ F₂) ≫ F₃ :=
    ξ₀ ≪≫ whiskerRightIso k ξ₁ F₃ ≪≫ whiskerRightIso k (whiskerRightIso k ξ₂ F₂) F₃
  have : Mono G.hom := inferInstance
  have hξ₂ : ξ₂.hom ∈ parity (R := k) _ _ σ := (homParityShiftDatum (k := k) σ).hom_mem _
  -- `Θ₁` and `Θ₂` in terms of the comparisons.
  have hΘ₁ : ξ₀.hom ≫ ξ₁.hom ▷ F₃ =
      sign k (σ * σ) • (Θ₁.hom ≫ (associator _ F₂ F₃).inv) := by
    rw [homShiftPairIso_hom_signed, Linear.smul_comp, smul_smul, Supercategory.sign_mul_self,
      one_smul]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]; rfl
  have hΘ₂ : ξ₁.hom ≫ ξ₂.hom ▷ F₂ =
      sign k (σ * σ) • (Θ₂.hom ≫ (associator Z F₁ F₂).inv) := by
    rw [homShiftPairIso_hom_signed, Linear.smul_comp, smul_smul, Supercategory.sign_mul_self,
      one_smul]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]; rfl
  have hG : G.hom = sign k (σ * σ) •
      (Θ₁.hom ≫ (associator _ F₂ F₃).inv ≫ (ξ₂.hom ▷ F₂) ▷ F₃) := by
    change ξ₀.hom ≫ ξ₁.hom ▷ F₃ ≫ (ξ₂.hom ▷ F₂) ▷ F₃ = _
    rw [← Category.assoc, hΘ₁, Linear.smul_comp, Category.assoc]
  -- The parity of the transported crossing `x`.
  have hM : Θ₂.hom ≫ Z ◁ x ≫ Θ₂.inv ∈ parity (R := k) _ _ p := by
    have h := comp_mem (homShiftPairIso_hom_mem (k := k) F₁ F₂ σ Z)
      (comp_mem (TwoSupercategory.whiskerLeft_mem Z hx)
        (Supercategory.inv_mem _ (homShiftPairIso_hom_mem (k := k) F₁ F₂ σ Z)))
    simpa only [zero_add, add_zero] using h
  refine braid_of_intertwine G.hom
    (A := sign k (σ * p) • ((associator (Z ≫ F₁) F₂ F₃).hom ≫ (Z ≫ F₁) ◁ y ≫
      (associator (Z ≫ F₁) F₂ F₃).inv))
    (B := sign k (σ * p) • ((associator Z F₁ F₂).hom ≫ Z ◁ x ≫ (associator Z F₁ F₂).inv) ▷ F₃)
    ?_ ?_ ?_
  · -- The left crossing: the super interchange law past `ξ₂`.
    have hsi := TwoSupercategory.super_interchange (R := k) (h := F₂ ≫ F₃) hξ₂ hy
    rw [koszulSign_smul (R := k)] at hsi
    have key : (homParityShift (k := k) σ).obj (Z ≫ F₁) ◁ y ≫
        (associator _ F₂ F₃).inv ≫ (ξ₂.hom ▷ F₂) ▷ F₃ =
        sign k (σ * p) • ((associator _ F₂ F₃).inv ≫ (ξ₂.hom ▷ F₂) ▷ F₃ ≫
          (associator (Z ≫ F₁) F₂ F₃).hom ≫ (Z ≫ F₁) ◁ y ≫ (associator (Z ≫ F₁) F₂ F₃).inv) := by
      rw [TwoSupercategory.associator_naturality_left_assoc (R := k), Iso.inv_hom_id_assoc,
        reassoc_of% hsi, ← TwoSupercategory.associator_inv_naturality_left (R := k)]
      simp only [Linear.smul_comp, Category.assoc, smul_smul, Supercategory.sign_mul_self,
        one_smul]
    rw [hG]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, Iso.inv_hom_id_assoc, key,
      smul_smul, mul_comm (sign k (σ * σ))]
  · -- The right crossing: the signed naturality of the outer shift.
    change (homParityShift (k := k) σ).map ((Θ₂.hom ≫ Z ◁ x ≫ Θ₂.inv) ▷ F₃) ≫ ξ₀.hom ≫
        ξ₁.hom ▷ F₃ ≫ (ξ₂.hom ▷ F₂) ▷ F₃ =
      (ξ₀.hom ≫ ξ₁.hom ▷ F₃ ≫ (ξ₂.hom ▷ F₂) ▷ F₃) ≫ _
    rw [reassoc_of% ((homParityShiftDatum (k := k) σ).hom_naturality
      (TwoSupercategory.whiskerRight_mem F₃ hM))]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
    congr 2
    simp only [← TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
    congr 1
    rw [hΘ₂, reassoc_of% hΘ₂]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, Iso.inv_hom_id_assoc]
  · simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
    congr 1
    exact post_whisker_braid k Z x y hb

end OddMath.SKM

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- **The braid relation for the reservoir crossings** on `RRR`: the factor braid relation
`W.braid`, transported by the comparisons `Θ`. -/
theorem postCrossSame_braid (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t))
    (hx : StepValid (true, i) false (nextSector (true, i) false (nextSector (true, i) false t)))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) false
      (nextSector (true, i) false t)))) :
    P.postCrossSame i t hv hw ((P.step (true, i) false _ hx).obj Z) ≫
        (P.step (true, i) false t hv).map (P.postCrossSame i _ hw hx Z) ≫
        P.postCrossSame i t hv hw ((P.step (true, i) false _ hx).obj Z) =
      (P.step (true, i) false t hv).map (P.postCrossSame i _ hw hx Z) ≫
        P.postCrossSame i t hv hw ((P.step (true, i) false _ hx).obj Z) ≫
        (P.step (true, i) false t hv).map (P.postCrossSame i _ hw hx Z) := by
  rw [postCrossSame_eq, postCrossSame_eq]
  exact shifted_post_braid (k := k) _ _ Z _ _ (P.W.cross_mem _ _ _ _ _ _)
    (P.W.cross_mem _ _ _ _ _ _)
    (P.W.braid i (P.muM_postE i hx) (P.muM_postE i hw) (P.muM_postE i hv))

variable (ν : X) (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
  (hw : StepValid (true, i) false (nextSector (true, i) false t))
  (hx : StepValid (true, i) false (nextSector (true, i) false (nextSector (true, i) false t)))

/-- The path `RRR` of `Eᵢ Eᵢ Eᵢ`. -/
def rrrPath : SPath (wd D ν [up i, up i, up i]) t
    (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, i) false t))) :=
  .cons _ false t hv (.cons _ false _ hw (.cons _ false _ hx (.nil _)))

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- `RRR` is the only path of `Eᵢ Eᵢ Eᵢ` to its endpoint. -/
theorem eq_rrrPath (p : SPath (wd D ν [up i, up i, up i]) t
    (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, i) false t)))) :
    p = rrrPath (D := D) ν i t hv hw hx := by
  suffices h : ∀ (t' : Sector I) (p : SPath (wd D ν [up i, up i, up i]) t t')
      (h : t' = nextSector (true, i) false
        (nextSector (true, i) false (nextSector (true, i) false t))),
      h ▸ p = rrrPath ν i t hv hw hx from h _ p rfl
  intro t' p h
  cases p with
  | cons _ σ₁ _ hv₁ p =>
    cases p with
    | cons _ σ₂ _ hv₂ p =>
      cases p with
      | cons _ σ₃ _ hv₃ p =>
        cases p
        have h₁ := congrArg (fun x : Sector I => x.1 i) h
        cases σ₁ <;> cases σ₂ <;> cases σ₃ <;>
          first
            | rfl
            | (exfalso; simp [nextSector] at h₁ <;> omega)

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- A sum over the paths of `Eᵢ Eᵢ Eᵢ` to the endpoint of `RRR` is its `RRR` term. -/
theorem sum_rrrPath {M : Type*} [AddCommMonoid M]
    {_ : Fintype (SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, i) false t))))}
    (f : SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, i) false t))) →
        M) :
    ∑ p, f p = f (rrrPath ν i t hv hw hx) :=
  Fintype.sum_eq_single _ fun p hp => absurd (eq_rrrPath ν i t hv hw hx p) hp

variable {P} (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, i) false (nextSector (true, i) false
    (nextSector (true, i) false t))))

/-- The left crossing on `RRR` is the reservoir crossing of the two left letters. -/
theorem rrrLeft_entry :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (rrrPath ν i t hv hw hx)
        (rrrPath ν i t hv hw hx) Z =
      P.postCrossSame i t hv hw ((P.step (true, i) false _ hx).obj Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ false t hv (.cons _ false _ hw (.nil _)))
    (.cons _ false t hv (.cons _ false _ hw (.nil _)))
    (.cons _ false _ hx (.nil _)) Z).trans ?_
  rw [swappedGens_cross_self]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The right crossing on `RRR` is the reservoir crossing of the two right letters. -/
theorem rrrRight_entry :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (rrrPath ν i t hv hw hx)
        (rrrPath ν i t hv hw hx) Z =
      (P.step (true, i) false t hv).map (P.postCrossSame i _ hw hx Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) false hv
    (.cons _ false _ hw (.cons _ false _ hx (.nil _)))
    (.cons _ false _ hw (.cons _ false _ hx (.nil _))) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

/-- **(1.9) on the path `RRR` of the colour pattern `iii`.** -/
theorem rrr_braid :
    braidLeft (P.swappedGens c L) i i i ν (rrrPath ν i t hv hw hx) (rrrPath ν i t hv hw hx) Z =
      braidRight (P.swappedGens c L) i i i ν (rrrPath ν i t hv hw hx)
        (rrrPath ν i t hv hw hx) Z := by
  unfold braidLeft braidRight
  simp only [sum_rrrPath ν i t hv hw hx, rrrLeft_entry, rrrRight_entry, Category.assoc]
  exact P.postCrossSame_braid i t hv hw hx Z

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
