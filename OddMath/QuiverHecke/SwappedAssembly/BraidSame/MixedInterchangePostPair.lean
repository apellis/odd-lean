/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.Cross

/-! # A crossing of two reservoir letters passes through a pair of mixed interchanges

Equation (5B) of `docs/Nondegeneracy/ThreeStrandSectorBraid.md`, proved in
`docs/Nondegeneracy/PairedHomInterchange.md` §4, for the relation (1.9) of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, at `Eᵢ Eᵢ Eᵢ`.

* `homShiftPairIso`: the even comparison `Θ_σ` of `PairedHomInterchange.md` §4 removing the two
  shifts of a doubly shifted postcomposition, `Πσ(Πσ(Y F₁) F₂) ≅ Y (F₁ F₂)`.
* `homMixedInterchange_postPair`: the two mixed interchanges moving one letter `E` past two
  shifted letters, followed by `Θ_κ`, are a sign times `Θ_κ'` followed by the associator
  (equation (7) there; the sign is retained).
* `homMixedInterchange_postPair_conj`: a 2-morphism on `F₁ ≫ F₂`, conjugated by `Θ`, passes
  through the pair of interchanges ((8) there): the common sign cancels.
* `ProbeReservoir.postCrossSame_mixedJ_pair`: (5B) for the paths `PRR`, `RPR`, `RRP`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams BicategoryStruct Supercategory

universe u v w r

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d e : B}

/-- The comparison `Θ_σ(Y)` removing the two shifts of `Πσ(Πσ(Y F₁) F₂)` and reassociating. It
is the component at `Y` of the word comparison of the content-shifted postcomposition. -/
def homShiftPairIso (F₁ : c ⟶ d) (F₂ : d ⟶ e) (σ : ZMod 2) (Y : a ⟶ c) :
    (homParityShift (k := k) σ).obj ((homParityShift (k := k) σ).obj (Y ≫ F₁) ≫ F₂) ≅
      Y ≫ F₁ ≫ F₂ :=
  homShiftConjugationIso (homPost (k := k) F₂) σ (Y ≫ F₁) ≪≫ associator Y F₁ F₂

theorem homShiftPairIso_hom (F₁ : c ⟶ d) (F₂ : d ⟶ e) (σ : ZMod 2) (Y : a ⟶ c) :
    (homShiftPairIso (k := k) F₁ F₂ σ Y).hom =
      (homParityShift (k := k) σ).map (((homParityShiftDatum (k := k) σ).iso (Y ≫ F₁)).hom ▷ F₂) ≫
        ((homParityShiftDatum (k := k) σ).iso ((Y ≫ F₁) ≫ F₂)).hom ≫
          (associator Y F₁ F₂).hom := by
  rw [homShiftPairIso, Iso.trans_hom, homShiftConjugationIso_hom]
  simp only [homPost, Category.assoc]

/-- Equation (7) of `PairedHomInterchange.md` §4: the two mixed interchanges moving `E` past two
shifted letters, followed by the comparison `Θ_κ`, are `Θ_κ'` followed by the associator, up to
the sign `(-1)^(κκ' + κ'κ')`. -/
theorem homMixedInterchange_postPair (E : a ⟶ b) (Z : b ⟶ c) (F₁ : c ⟶ d) (F₂ : d ⟶ e)
    (κ' κ : ZMod 2) :
    (homMixedInterchange (k := k) E F₂ κ' κ ((homParityShift (k := k) κ').obj (Z ≫ F₁))).hom ≫
        (homParityShift (k := k) κ).map ((homMixedInterchange (k := k) E F₁ κ' κ Z).hom ▷ F₂) ≫
          (homShiftPairIso (k := k) F₁ F₂ κ (E ≫ Z)).hom =
      (sign k (κ * κ') * sign k (κ' * κ')) •
        (E ◁ (homShiftPairIso (k := k) F₁ F₂ κ' Z).hom ≫ (associator E Z (F₁ ≫ F₂)).inv) := by
  have hg : (E ◁ ((homParityShiftDatum (k := k) κ').iso (Z ≫ F₁)).hom ≫
      (associator E Z F₁).inv) ▷ F₂ ∈ parity (R := k) _ _ κ' := by
    refine TwoSupercategory.whiskerRight_mem F₂ ?_
    simpa only [add_zero] using comp_mem
      (TwoSupercategory.whiskerLeft_mem E ((homParityShiftDatum (k := k) κ').hom_mem _))
      (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E Z F₁))
  have hd : ((homParityShiftDatum (k := k) κ').iso (Z ≫ F₁)).hom ▷ F₂ ∈
      parity (R := k) _ _ κ' :=
    TwoSupercategory.whiskerRight_mem F₂ ((homParityShiftDatum (k := k) κ').hom_mem _)
  rw [homShiftPairIso_hom, homShiftPairIso_hom]
  simp only [homMixedInterchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, homPre,
    Category.assoc]
  rw [← Functor.map_comp_assoc, ← TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% ((homParityShiftDatum (k := k) κ).hom_naturality hg),
    reassoc_of% ((homParityShiftDatum (k := k) κ').hom_naturality hd)]
  simp only [Linear.comp_smul, Linear.smul_comp,
    TwoSupercategory.whiskerLeft_smul, smul_smul, mul_assoc, Supercategory.sign_mul_self,
    mul_one]
  congr 1
  simp only [Category.assoc, TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.comp_whiskerRight (R := k), Iso.inv_hom_id_assoc]
  congr 1
  rw [← TwoSupercategory.associator_inv_naturality_middle_assoc (R := k)]
  congr 1
  refine (TwoSupercategory.whiskerLeft_hom_inv_assoc (R := k) E (associator Z F₁ F₂) _).symm.trans
    ?_
  rw [TwoSupercategory.pentagon_inv_assoc (R := k), Iso.inv_hom_id, Category.comp_id]

/-- Equation (8) of `PairedHomInterchange.md` §4: a 2-morphism `χ` on `F₁ ≫ F₂`, transported by
`Θ_κ'` onto `E Πκ'(Πκ'(Z F₁) F₂)`, passes through the pair of mixed interchanges to its
transport by `Θ_κ` onto `Πκ(Πκ((E Z) F₁) F₂)`. The sign of (7) is common to both sides. -/
theorem homMixedInterchange_postPair_conj (E : a ⟶ b) (Z : b ⟶ c) (F₁ : c ⟶ d) (F₂ : d ⟶ e)
    (κ' κ : ZMod 2) (χ : F₁ ≫ F₂ ⟶ F₁ ≫ F₂) :
    E ◁ ((homShiftPairIso (k := k) F₁ F₂ κ' Z).hom ≫ Z ◁ χ ≫
          (homShiftPairIso (k := k) F₁ F₂ κ' Z).inv) ≫
        (homMixedInterchange (k := k) E F₂ κ' κ ((homParityShift (k := k) κ').obj (Z ≫ F₁))).hom ≫
          (homParityShift (k := k) κ).map ((homMixedInterchange (k := k) E F₁ κ' κ Z).hom ▷ F₂) =
      (homMixedInterchange (k := k) E F₂ κ' κ ((homParityShift (k := k) κ').obj (Z ≫ F₁))).hom ≫
        (homParityShift (k := k) κ).map ((homMixedInterchange (k := k) E F₁ κ' κ Z).hom ▷ F₂) ≫
          (homShiftPairIso (k := k) F₁ F₂ κ (E ≫ Z)).hom ≫ (E ≫ Z) ◁ χ ≫
            (homShiftPairIso (k := k) F₁ F₂ κ (E ≫ Z)).inv := by
  have key : (homMixedInterchange (k := k) E F₂ κ' κ
        ((homParityShift (k := k) κ').obj (Z ≫ F₁))).hom ≫
        (homParityShift (k := k) κ).map ((homMixedInterchange (k := k) E F₁ κ' κ Z).hom ▷ F₂) =
      ((sign k (κ * κ') * sign k (κ' * κ')) •
        (E ◁ (homShiftPairIso (k := k) F₁ F₂ κ' Z).hom ≫ (associator E Z (F₁ ≫ F₂)).inv)) ≫
        (homShiftPairIso (k := k) F₁ F₂ κ (E ≫ Z)).inv := by
    rw [Iso.eq_comp_inv]
    simpa only [Category.assoc] using homMixedInterchange_postPair (k := k) E Z F₁ F₂ κ' κ
  rw [reassoc_of% key, key]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc,
    TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.whiskerLeft_inv_hom_assoc (R := k),
    Iso.inv_hom_id_assoc, TwoSupercategory.associator_inv_naturality_right_assoc (R := k)]

/-- The word comparison of the content-shifted postcomposition is `Θ`. -/
theorem homContentPostWordIso_app {I X : Type*} [AddCommGroup X] {D : Datum I X}
    (T : X → B) (W : RouquierFamily (k := k) (B := B) D) (i : I) (betaP : I →₀ ℕ) (muP : X)
    {muM nuM rhoM : X} (h : muM + D.α i = nuM) (h₂ : nuM + D.α i = rhoM)
    (Z : homWeightSector T W.obj muP muM) :
    (homContentPostWordIso T W i betaP muP h h₂).app Z =
      homShiftPairIso (k := k) (W.E i h) (W.E i h₂) (homContentShift D i betaP) Z := by
  ext
  rw [Iso.app_hom, homContentPostWordIso_hom_app, homShiftPairIso, Iso.trans_hom]

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

/-- The reservoir crossing is the factor crossing transported by `Θ`. -/
theorem postCrossSame_eq (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) false t))) :
    P.postCrossSame i t hv hw Z =
      (homShiftPairIso (k := k) (P.W.E i (P.muM_postE i hw)) (P.W.E i (P.muM_postE i hv))
          (homContentShift D i t.1) Z).hom ≫
        Z ◁ P.W.cross i i (P.muM_postE i hw) (P.muM_postE i hv) (P.muM_postE i hw)
          (P.muM_postE i hv) ≫
        (homShiftPairIso (k := k) (P.W.E i (P.muM_postE i hw)) (P.W.E i (P.muM_postE i hv))
          (homContentShift D i t.1) Z).inv := by
  rw [postCrossSame, homContentPostCrossingApp, ← Iso.app_hom, ← Iso.app_inv,
    homContentPostWordIso_app]

/-- (5B) of `docs/Nondegeneracy/ThreeStrandSectorBraid.md` for the paths `PRR`, `RPR`, `RRP`
of `Eᵢ Eᵢ Eᵢ`: the reservoir crossing on the two right letters of `PRR` is carried by the two
mixed interchanges `PRR → RPR → RRP` to the reservoir crossing on the two left letters of
`RRP`. -/
theorem postCrossSame_mixedJ_pair (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) false
      (nextSector (true, i) true t)))) :
    (P.step (true, i) true t trivial).map
          (P.postCrossSame i (nextSector (true, i) true t) hv hw Z) ≫
        (P.mixedJ i i t hv ((P.step (true, i) false
          (nextSector (true, i) false (nextSector (true, i) true t)) hw).obj Z)).hom ≫
        (P.step (true, i) false t hv).map (P.mixedJ i i (nextSector (true, i) false t) hw Z).hom =
      (P.mixedJ i i t hv ((P.step (true, i) false
          (nextSector (true, i) false (nextSector (true, i) true t)) hw).obj Z)).hom ≫
        (P.step (true, i) false t hv).map (P.mixedJ i i (nextSector (true, i) false t) hw Z).hom ≫
        P.postCrossSame i t hv hw ((P.step (true, i) true _ trivial).obj Z) := by
  rw [postCrossSame_eq, postCrossSame_eq]
  exact homMixedInterchange_postPair_conj (k := k) _ _ _ _ _ _ _

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
