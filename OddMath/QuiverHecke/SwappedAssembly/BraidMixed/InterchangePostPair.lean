/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.MixedInterchangePostPair
import OddMath.QuiverHecke.SwappedAssembly.QuadNe

/-! # Mixed interchange with two reservoir colours

The one-probe/two-reservoir triangle of `MixedColourRemainingBraid.md` §2.
The source and target reservoir paths have independent intermediate objects;
the two individual content shifts need not agree. The removal maps are
homogeneous, not asserted even. Their signed expansion is proved first, then
the prescribed beta/xi comparison is identified with those removals. Finally
`resCore_mixedInterchange_pair` instantiates the normalized reservoir crossing
and cancels the content-dependent signs. No naturality equation is assumed.

The equal-colour sector braid blocks remain the results of `BraidSame`.
This module supplies a mixed triangle, not the full `CrossBraid` assembly.
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

/-- Homogeneous removal of two independently shifted postcomposition letters. -/
def homPostPairRemoval (F₁ : c ⟶ d) (F₂ : d ⟶ e) (σ₁ σ₂ : ZMod 2) (Y : a ⟶ c) :
    (homParityShift (k := k) σ₂).obj ((homParityShift (k := k) σ₁).obj (Y ≫ F₁) ≫ F₂) ≅
      Y ≫ F₁ ≫ F₂ :=
  (homParityShift (k := k) σ₂).mapIso
    ((homPost (k := k) F₂).mapIso ((homParityShiftDatum (k := k) σ₁).iso (Y ≫ F₁))) ≪≫
    (homParityShiftDatum (k := k) σ₂).iso ((Y ≫ F₁) ≫ F₂) ≪≫ associator Y F₁ F₂

theorem homMixedInterchange_postPair_shifts (E : a ⟶ b) (Z : b ⟶ c) (F₁ : c ⟶ d) (F₂ : d ⟶ e)
    (κ₁' κ₂' κ₁ κ₂ : ZMod 2) :
    (homMixedInterchange (k := k) E F₂ κ₂' κ₂ ((homParityShift (k := k) κ₁').obj (Z ≫ F₁))).hom ≫
        (homParityShift (k := k) κ₂).map ((homMixedInterchange (k := k) E F₁ κ₁' κ₁ Z).hom ▷ F₂) ≫
          (homPostPairRemoval (k := k) F₁ F₂ κ₁ κ₂ (E ≫ Z)).hom =
      (sign k (κ₂ * κ₁') * sign k (κ₂' * κ₁')) •
        (E ◁ (homPostPairRemoval (k := k) F₁ F₂ κ₁' κ₂' Z).hom ≫ (associator E Z (F₁ ≫ F₂)).inv) := by
  have hg : (E ◁ ((homParityShiftDatum (k := k) κ₁').iso (Z ≫ F₁)).hom ≫
      (associator E Z F₁).inv) ▷ F₂ ∈ parity (R := k) _ _ κ₁' := by
    refine TwoSupercategory.whiskerRight_mem F₂ ?_
    simpa only [add_zero] using comp_mem
      (TwoSupercategory.whiskerLeft_mem E ((homParityShiftDatum (k := k) κ₁').hom_mem _))
      (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E Z F₁))
  have hd : ((homParityShiftDatum (k := k) κ₁').iso (Z ≫ F₁)).hom ▷ F₂ ∈
      parity (R := k) _ _ κ₁' :=
    TwoSupercategory.whiskerRight_mem F₂ ((homParityShiftDatum (k := k) κ₁').hom_mem _)
  simp only [homPostPairRemoval, Iso.trans_hom, Functor.mapIso_hom, homPost]
  simp only [homMixedInterchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, homPre,
    Category.assoc]
  rw [← Functor.map_comp_assoc, ← TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% ((homParityShiftDatum (k := k) κ₂).hom_naturality hg),
    reassoc_of% ((homParityShiftDatum (k := k) κ₂').hom_naturality hd)]
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



/-- The paired interchanges expressed through the homogeneous removals. -/
theorem homMixedInterchange_postPair_shifts_eq (E : a ⟶ b) (Z : b ⟶ c)
    (F₁ : c ⟶ d) (F₂ : d ⟶ e) (κ₁' κ₂' κ₁ κ₂ : ZMod 2) :
    (homMixedInterchange (k := k) E F₂ κ₂' κ₂
      ((homParityShift (k := k) κ₁').obj (Z ≫ F₁))).hom ≫
      (homParityShift (k := k) κ₂).map
        ((homMixedInterchange (k := k) E F₁ κ₁' κ₁ Z).hom ▷ F₂) =
    (sign k (κ₂ * κ₁') * sign k (κ₂' * κ₁')) •
      (E ◁ (homPostPairRemoval (k := k) F₁ F₂ κ₁' κ₂' Z).hom ≫
        (associator E Z (F₁ ≫ F₂)).inv ≫
        (homPostPairRemoval (k := k) F₁ F₂ κ₁ κ₂ (E ≫ Z)).inv) := by
  rw [← Linear.smul_comp, ← Category.assoc, Iso.eq_comp_inv]
  simpa only [Category.assoc, Linear.smul_comp] using
    homMixedInterchange_postPair_shifts (k := k) E Z F₁ F₂ κ₁' κ₂' κ₁ κ₂

/-- Two different reservoir paths are allowed; only their removal signs must agree. -/
theorem homMixedInterchange_postPair_between {d' : B} (E : a ⟶ b) (Z : b ⟶ c)
    (F₁ : c ⟶ d) (F₂ : d ⟶ e) (G₁ : c ⟶ d') (G₂ : d' ⟶ e)
    (κ₁' κ₂' κ₁ κ₂ : ZMod 2)
    (hs : sign k (κ₂ * κ₁') * sign k (κ₂' * κ₁') =
      sign k (κ₁ * κ₂') * sign k (κ₁' * κ₂'))
    (χ : F₁ ≫ F₂ ⟶ G₁ ≫ G₂) :
    E ◁ ((homPostPairRemoval (k := k) F₁ F₂ κ₁' κ₂' Z).hom ≫ Z ◁ χ ≫
      (homPostPairRemoval (k := k) G₁ G₂ κ₂' κ₁' Z).inv) ≫
      (homMixedInterchange (k := k) E G₂ κ₁' κ₁
        ((homParityShift (k := k) κ₂').obj (Z ≫ G₁))).hom ≫
        (homParityShift (k := k) κ₁).map
          ((homMixedInterchange (k := k) E G₁ κ₂' κ₂ Z).hom ▷ G₂) =
    (homMixedInterchange (k := k) E F₂ κ₂' κ₂
      ((homParityShift (k := k) κ₁').obj (Z ≫ F₁))).hom ≫
      (homParityShift (k := k) κ₂).map
        ((homMixedInterchange (k := k) E F₁ κ₁' κ₁ Z).hom ▷ F₂) ≫
      (homPostPairRemoval (k := k) F₁ F₂ κ₁ κ₂ (E ≫ Z)).hom ≫
        (E ≫ Z) ◁ χ ≫ (homPostPairRemoval (k := k) G₁ G₂ κ₂ κ₁ (E ≫ Z)).inv := by
  rw [homMixedInterchange_postPair_shifts_eq,
    ← Category.assoc _ ((homParityShift (k := k) κ₂).map _),
    homMixedInterchange_postPair_shifts_eq, hs]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc,
    TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whiskerLeft_inv_hom_assoc (R := k), Iso.inv_hom_id_assoc,
    TwoSupercategory.associator_inv_naturality_right_assoc (R := k)]


omit [TwoSupercategory k B] in
/-- The shift-addition comparison followed by removal, including the odd square sign. -/
theorem homParityShiftAdd_remove (p q : ZMod 2) (Y : a ⟶ b) :
    (homParityShiftAdd (k := k) p q).hom.app Y ≫
      ((homParityShiftDatum (k := k) (p + q)).iso Y).hom =
    (homParityShift (k := k) q).map ((homParityShiftDatum (k := k) p).iso Y).hom ≫
      ((homParityShiftDatum (k := k) q).iso Y).hom := by
  fin_cases p <;> fin_cases q
  · simp [homParityShiftAdd, homParityShiftDatum, homParityShift, ParityShiftDatum.id]
  · simp [homParityShiftAdd, homParityShiftDatum, homParityShift, ParityShiftDatum.id]
  · simp [homParityShiftAdd, homParityShiftDatum, homParityShift, ParityShiftDatum.id]
  · simp [homParityShiftAdd, homParityShiftDatum, homParityShift, ParityShiftDatum.id,
      ParityShiftDatum.pi, PiSupercategory.ξIso, PiSupercategory.ξ_hom]

open OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir in
/-- The prescribed beta/xi comparison, not a freely chosen conjugation, removes to Θ. -/
theorem postPairIso_remove (F₁ : c ⟶ d) (F₂ : d ⟶ e) (p q : ZMod 2) (Y : a ⟶ c) :
    (postPairIso (k := k) F₂ Y F₁ q p).hom ≫
      ((homParityShiftDatum (k := k) (p + q)).iso ((Y ≫ F₁) ≫ F₂)).hom ≫
      (associator Y F₁ F₂).hom = (homPostPairRemoval (k := k) F₁ F₂ p q Y).hom := by
  simp only [postPairIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Category.assoc]
  rw [reassoc_of% homParityShiftAdd_remove, homParityShiftCommute_inv_app,
    Functor.map_comp]
  simp only [homPostPairRemoval, Iso.trans_hom, Functor.mapIso_hom, homPost, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]


omit [TwoSupercategory k B] in
/-- Equal shift indices give the same removal after the canonical transport. -/
theorem homShift_eqToHom_remove (p q : ZMod 2) (h : p = q) (Y : a ⟶ b) :
    eqToHom (congrArg (fun s => (homParityShift (k := k) s).obj Y) h) ≫
      ((homParityShiftDatum (k := k) q).iso Y).hom =
      ((homParityShiftDatum (k := k) p).iso Y).hom := by
  subst q
  simp only [eqToHom_refl, Category.id_comp]

open OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir in
/-- Normalization of the prescribed two-colour post crossing with its shift sign. -/
theorem postPairIso_cross_remove {d' : B} (F₁ : c ⟶ d) (F₂ : d ⟶ e)
    (G₁ : c ⟶ d') (G₂ : d' ⟶ e) (p q : ZMod 2) (Y : a ⟶ c)
    {r : ZMod 2} {χ : F₁ ≫ F₂ ⟶ G₁ ≫ G₂} (hχ : χ ∈ parity (R := k) _ _ r) :
    (postPairIso (k := k) F₂ Y F₁ q p).hom ≫
      (homParityShift (k := k) (p + q)).map
        ((associator Y F₁ F₂).hom ≫ Y ◁ χ ≫ (associator Y G₁ G₂).inv) ≫
      eqToHom (by rw [add_comm]) ≫ (postPairIso (k := k) G₂ Y G₁ p q).inv =
    sign k ((p + q) * r) • ((homPostPairRemoval (k := k) F₁ F₂ p q Y).hom ≫
      Y ◁ χ ≫ (homPostPairRemoval (k := k) G₁ G₂ q p Y).inv) := by
  apply (cancel_mono (homPostPairRemoval (k := k) G₁ G₂ q p Y).hom).mp
  rw [← postPairIso_remove G₁ G₂ q p Y]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% (homShift_eqToHom_remove (k := k) (p + q) (q + p) (add_comm p q))]
  have hm : (associator Y F₁ F₂).hom ≫ Y ◁ χ ≫ (associator Y G₁ G₂).inv ∈
      parity (R := k) _ _ r := by
    simpa only [zero_add, add_zero] using comp_mem
      (TwoSupercategory.associator_hom_mem (R := k) Y F₁ F₂)
      (comp_mem (TwoSupercategory.whiskerLeft_mem Y hχ)
        (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) Y G₁ G₂)))
  rw [reassoc_of% ((homParityShiftDatum (k := k) (p + q)).hom_naturality hm)]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [reassoc_of% postPairIso_remove]
  rw [postPairIso_remove]
  simp only [Iso.inv_hom_id, Category.comp_id]

end OddMath.SKM

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] {D : Datum I X}

/-- Content shifts annihilate the normalization sign of the factor crossing. -/
theorem resCore_content_eq (W : RouquierFamily (k := k) (B := B) D) (i j : I)
    (β : I →₀ ℕ) {a b c d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) {x : B} (Z : x ⟶ W.obj a) :
    resCore W i j (homContentShift D i β) (homContentShift D j β) h₁ h₂ h₃ h₄ Z =
      (homPostPairRemoval (k := k) (W.E j h₁) (W.E i h₂)
        (homContentShift D j β) (homContentShift D i β) Z).hom ≫
      Z ◁ W.cross i j h₁ h₂ h₃ h₄ ≫
      (homPostPairRemoval (k := k) (W.E i h₃) (W.E j h₄)
        (homContentShift D i β) (homContentShift D j β) Z).inv := by
  unfold resCore
  rw [postPairIso_cross_remove _ _ _ _ _ _ _ (W.cross_mem i j h₁ h₂ h₃ h₄)]
  have hz : (homContentShift D j β + homContentShift D i β) *
      (D.parity i * D.parity j) = 0 := by
    unfold homContentShift
    generalize D.parity i = pi, D.parity j = pj, contentParity D β = t
    fin_cases pi <;> fin_cases pj <;> fin_cases t <;> decide
  rw [hz, sign_zero, one_smul]

/-- One probe passes through the normalized crossing of two reservoir colours.
The factor paths may have unequal intermediate weights. -/
theorem resCore_mixedInterchange_pair (W : RouquierFamily (k := k) (B := B) D)
    (i j r : I) (β : I →₀ ℕ) {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d)
    {x y : B} (E : x ⟶ y) (Z : y ⟶ W.obj a) :
    let ki := homContentShift D i β
    let kj := homContentShift D j β
    let ui := homContentShift D i (β + Finsupp.single r 1)
    let uj := homContentShift D j (β + Finsupp.single r 1)
    E ◁ resCore W i j ui uj h₁ h₂ h₃ h₄ Z ≫
      (homMixedInterchange (k := k) E (W.E j h₄) uj kj
        ((homParityShift (k := k) ui).obj (Z ≫ W.E i h₃))).hom ≫
      (homParityShift (k := k) kj).map
        ((homMixedInterchange (k := k) E (W.E i h₃) ui ki Z).hom ▷ W.E j h₄) =
    (homMixedInterchange (k := k) E (W.E i h₂) ui ki
      ((homParityShift (k := k) uj).obj (Z ≫ W.E j h₁))).hom ≫
      (homParityShift (k := k) ki).map
        ((homMixedInterchange (k := k) E (W.E j h₁) uj kj Z).hom ▷ W.E i h₂) ≫
      resCore W i j ki kj h₁ h₂ h₃ h₄ (E ≫ Z) := by
  dsimp only
  rw [resCore_content_eq, resCore_content_eq]
  apply homMixedInterchange_postPair_between
  simp only [homContentShift]
  generalize D.parity i = pi, D.parity j = pj, D.parity r = pr, contentParity D β = t
  fin_cases pi <;> fin_cases pj <;> fin_cases pr <;> fin_cases t <;> simp

end OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
