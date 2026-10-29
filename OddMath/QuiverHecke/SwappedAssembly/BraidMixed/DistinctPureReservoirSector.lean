/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.ReservoirBlock
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctReservoirSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctPureProbeSector

/-! # Shifted distinct-colour reservoir braids

`ProbeReservoir.distinctPureReservoir_factor_braid` transports the reservoir's
multicolour braid through the prescribed `postPairIso` comparisons. It retains
independent intermediate weights and the content shifts. The two triple-removal
lemmas record the signs from super interchange and shift naturality separately.

The canonical path entry lemmas identify left and right crossings with
`postCrossNe`; the sum lemmas collapse both intermediate path sums. The final
comparison of their sector transports with the common factor-weight grid is
not asserted here.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u,u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {D : Datum I X} {Sc : Scalars D k}

/-- Reassociation of a left-whiskered triple. -/
def reservoirTripleIso {a b c d e : B} (Z : a ⟶ b) (E : b ⟶ c)
    (F : c ⟶ d) (G : d ⟶ e) : ((Z ≫ E) ≫ F) ≫ G ≅ Z ≫ E ≫ F ≫ G :=
  associator (Z ≫ E) F G ≪≫ associator Z E (F ≫ G)

include k in
/-- A crossing of the outer pair commutes with left reassociation. -/
theorem reservoirTripleIso_outer {a b c d d' e : B} (Z : a ⟶ b) (E : b ⟶ c)
    (F : c ⟶ d) (G : d ⟶ e) (F' : c ⟶ d') (G' : d' ⟶ e)
    (y : F ≫ G ⟶ F' ≫ G') :
    ((associator (Z ≫ E) F G).hom ≫ (Z ≫ E) ◁ y ≫
      (associator (Z ≫ E) F' G').inv) ≫ (reservoirTripleIso Z E F' G').hom =
    (reservoirTripleIso Z E F G).hom ≫ Z ◁ (E ◁ y) := by
  simp only [reservoirTripleIso, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
    TwoSupercategory.associator_naturality_right (R := k)]

include k in
/-- A crossing of the inner pair commutes with left reassociation. -/
theorem reservoirTripleIso_inner {a b c c' d e : B} (Z : a ⟶ b)
    (E : b ⟶ c) (F : c ⟶ d) (E' : b ⟶ c') (F' : c' ⟶ d) (G : d ⟶ e)
    (x : E ≫ F ⟶ E' ≫ F') :
    ((associator Z E F).hom ≫ Z ◁ x ≫ (associator Z E' F').inv) ▷ G ≫
      (reservoirTripleIso Z E' F' G).hom =
    (reservoirTripleIso Z E F G).hom ≫
      Z ◁ ((associator E F G).inv ≫ x ▷ G ≫ (associator E' F' G).hom) := by
  have hp (c : B) (E : b ⟶ c) (F : c ⟶ d) :=
    TwoSupercategory.pentagon (R := k) Z E F G
  simp only [reservoirTripleIso, Iso.trans_hom]
  rw [← hp c' E' F', ← hp c E F]
  simp only [Category.assoc, TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.inv_hom_whiskerRight_assoc (R := k),
    TwoSupercategory.associator_naturality_middle_assoc (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whiskerLeft_hom_inv_assoc (R := k)]

variable [∀ a b : B, PiSupercategory k (a ⟶ b)]

/-- Removal of the three independent reservoir shifts. -/
def reservoirShiftTripleIso {a b c d e : B} (Z : a ⟶ b) (E : b ⟶ c)
    (F : c ⟶ d) (G : d ⟶ e) (p q r : ZMod 2) :
    (homParityShift (k := k) r).obj ((homParityShift (k := k) q).obj
      ((homParityShift (k := k) p).obj (Z ≫ E) ≫ F) ≫ G) ≅ ((Z ≫ E) ≫ F) ≫ G :=
  (homParityShiftDatum (k := k) r).iso _ ≪≫
    whiskerRightIso k ((homParityShiftDatum (k := k) q).iso _) G ≪≫
    whiskerRightIso k (whiskerRightIso k ((homParityShiftDatum (k := k) p).iso _) F) G

/-- Pair removal expressed through its two homogeneous comparison maps. -/
theorem reservoirPairRemoval_signed {a b c d : B} (Z : a ⟶ b)
    (E : b ⟶ c) (F : c ⟶ d) (p q : ZMod 2) :
    (homPostPairRemoval (k := k) E F p q Z).hom = sign k (q * p) •
      (((homParityShiftDatum (k := k) q).iso _).hom ≫
       ((homParityShiftDatum (k := k) p).iso (Z ≫ E)).hom ▷ F ≫
       (associator Z E F).hom) := by
  simp only [homPostPairRemoval, Iso.trans_hom, Functor.mapIso_hom, homPost]
  rw [reassoc_of% ((homParityShiftDatum (k := k) q).hom_naturality
    (TwoSupercategory.whiskerRight_mem F ((homParityShiftDatum (k := k) p).hom_mem _))),
    Linear.smul_comp]
  simp only [Category.assoc]

/-- The normalized outer crossing intertwines the triple shift removals. -/
theorem reservoirShiftTriple_outer {a b c d d' e : B} (Z : a ⟶ b) (E : b ⟶ c)
    (F : c ⟶ d) (G : d ⟶ e) (F' : c ⟶ d') (G' : d' ⟶ e)
    (p q r t : ZMod 2) (y : F ≫ G ⟶ F' ≫ G')
    (hy : y ∈ parity (R := k) _ _ t) :
    ((homPostPairRemoval (k := k) F G q r ((homParityShift (k := k) p).obj (Z ≫ E))).hom ≫
      (homParityShift (k := k) p).obj (Z ≫ E) ◁ y ≫
      (homPostPairRemoval (k := k) F' G' r q ((homParityShift (k := k) p).obj (Z ≫ E))).inv) ≫
      (reservoirShiftTripleIso Z E F' G' p r q).hom =
    sign k (p * t) • ((reservoirShiftTripleIso Z E F G p q r).hom ≫
      (associator (Z ≫ E) F G).hom ≫ (Z ≫ E) ◁ y ≫
      (associator (Z ≫ E) F' G').inv) := by
  let ξ := (homParityShiftDatum (k := k) p).iso (Z ≫ E)
  have hG (d : B) (F : c ⟶ d) (G : d ⟶ e) (q r : ZMod 2) :
      (reservoirShiftTripleIso Z E F G p q r).hom = sign k (r * q) •
        ((homPostPairRemoval (k := k) F G q r ((homParityShift (k := k) p).obj (Z ≫ E))).hom ≫
          (associator _ F G).inv ≫ (ξ.hom ▷ F) ▷ G) := by
    rw [reservoirPairRemoval_signed]
    simp only [Linear.smul_comp, smul_smul, Supercategory.sign_mul_self, one_smul,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have hsi := TwoSupercategory.super_interchange (R := k) (h := F ≫ G)
    ((homParityShiftDatum (k := k) p).hom_mem (Z ≫ E)) hy
  rw [koszulSign_smul (R := k)] at hsi
  have key : (homParityShift (k := k) p).obj (Z ≫ E) ◁ y ≫
      (associator _ F' G').inv ≫ (ξ.hom ▷ F') ▷ G' =
      sign k (p * t) • ((associator _ F G).inv ≫ (ξ.hom ▷ F) ▷ G ≫
        (associator (Z ≫ E) F G).hom ≫ (Z ≫ E) ◁ y ≫
        (associator (Z ≫ E) F' G').inv) := by
    rw [TwoSupercategory.associator_naturality_left_assoc (R := k), Iso.inv_hom_id_assoc,
      reassoc_of% hsi, ← TwoSupercategory.associator_inv_naturality_left (R := k)]
    simp only [Linear.smul_comp, Category.assoc, smul_smul, Supercategory.sign_mul_self, one_smul]
    rfl
  rw [hG d' F' G' r q, hG d F G q r]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, Iso.inv_hom_id_assoc, key,
    smul_smul, mul_comm q r, mul_comm (sign k (r * q))]

/-- Pair removal is homogeneous of the sum of its shifts. -/
theorem reservoirPairRemoval_mem {a b c d : B} (Z : a ⟶ b)
    (E : b ⟶ c) (F : c ⟶ d) (p q : ZMod 2) :
    (homPostPairRemoval (k := k) E F p q Z).hom ∈ parity (R := k) _ _ (q + p) := by
  rw [reservoirPairRemoval_signed]
  apply Submodule.smul_mem
  simpa only [add_zero] using comp_mem ((homParityShiftDatum (k := k) q).hom_mem _)
    (comp_mem (TwoSupercategory.whiskerRight_mem F ((homParityShiftDatum (k := k) p).hom_mem _))
      (TwoSupercategory.associator_hom_mem (R := k) Z E F))

/-- The normalized inner crossing intertwines the triple shift removals. -/
theorem reservoirShiftTriple_inner {a b c c' d e : B} (Z : a ⟶ b)
    (E : b ⟶ c) (F : c ⟶ d) (E' : b ⟶ c') (F' : c' ⟶ d) (G : d ⟶ e)
    (p q r t : ZMod 2) (x : E ≫ F ⟶ E' ≫ F')
    (hx : x ∈ parity (R := k) _ _ t) :
    (homParityShift (k := k) r).map
      (((homPostPairRemoval (k := k) E F p q Z).hom ≫ Z ◁ x ≫
        (homPostPairRemoval (k := k) E' F' q p Z).inv) ▷ G) ≫
      (reservoirShiftTripleIso Z E' F' G q p r).hom =
    sign k (r * t) • ((reservoirShiftTripleIso Z E F G p q r).hom ≫
      ((associator Z E F).hom ≫ Z ◁ x ≫ (associator Z E' F').inv) ▷ G) := by
  let Θ := homPostPairRemoval (k := k) E F p q Z
  let Θ' := homPostPairRemoval (k := k) E' F' q p Z
  have hm : Θ.hom ≫ Z ◁ x ≫ Θ'.inv ∈ parity (R := k) _ _ t := by
    have h := comp_mem (reservoirPairRemoval_mem Z E F p q)
      (comp_mem (TwoSupercategory.whiskerLeft_mem Z hx)
        (inv_mem _ (reservoirPairRemoval_mem Z E' F' q p)))
    have ht : q + p + (t + (p + q)) = t := by
      calc
        q + p + (t + (p + q)) = (q + q) + (p + p) + t := by ac_rfl
        _ = t := by rw [Supercategory.zmod2_add_self, Supercategory.zmod2_add_self, zero_add, zero_add]
    rw [ht] at h
    exact h
  have hpair (c : B) (E : b ⟶ c) (F : c ⟶ d) (p q : ZMod 2) :
      ((homParityShiftDatum (k := k) q).iso _).hom ≫
        ((homParityShiftDatum (k := k) p).iso (Z ≫ E)).hom ▷ F =
      sign k (q * p) • ((homPostPairRemoval (k := k) E F p q Z).hom ≫
        (associator Z E F).inv) := by
    rw [reservoirPairRemoval_signed]
    simp only [Linear.smul_comp, smul_smul, Supercategory.sign_mul_self, one_smul,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (homParityShift (k := k) r).map ((Θ.hom ≫ Z ◁ x ≫ Θ'.inv) ▷ G) ≫
    ((homParityShiftDatum (k := k) r).iso _).hom ≫ _ = _
  rw [reassoc_of% ((homParityShiftDatum (k := k) r).hom_naturality
    (TwoSupercategory.whiskerRight_mem G hm))]
  simp only [reservoirShiftTripleIso, Iso.trans_hom, whiskerRightIso,
    Linear.smul_comp, Category.assoc]
  congr 2
  simp only [← TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
  congr 1
  rw [hpair c' E' F' q p, reassoc_of% (hpair c E F p q)]
  simp only [Θ, Θ', Linear.comp_smul, Linear.smul_comp, Category.assoc, Iso.inv_hom_id_assoc,
    mul_comm p q]

/-- Removal followed by reassociation to the factor triple. -/
def reservoirTotalIso {a b c d e : B} (Z : a ⟶ b) (E : b ⟶ c)
    (F : c ⟶ d) (G : d ⟶ e) (p q r : ZMod 2) :=
  reservoirShiftTripleIso (k := k) Z E F G p q r ≪≫ reservoirTripleIso Z E F G

/-- Outer crossings after total removal. -/
theorem reservoirTotal_outer {a b c d d' e : B} (Z : a ⟶ b) (E : b ⟶ c)
    (F : c ⟶ d) (G : d ⟶ e) (F' : c ⟶ d') (G' : d' ⟶ e)
    (p q r t : ZMod 2) (y : F ≫ G ⟶ F' ≫ G')
    (hy : y ∈ parity (R := k) _ _ t) :
    ((homPostPairRemoval (k := k) F G q r ((homParityShift (k := k) p).obj (Z ≫ E))).hom ≫
      (homParityShift (k := k) p).obj (Z ≫ E) ◁ y ≫
      (homPostPairRemoval (k := k) F' G' r q ((homParityShift (k := k) p).obj (Z ≫ E))).inv) ≫
      (reservoirTotalIso Z E F' G' p r q).hom =
    sign k (p * t) • ((reservoirTotalIso Z E F G p q r).hom ≫ Z ◁ (E ◁ y)) := by
  simp only [reservoirTotalIso, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% (reservoirShiftTriple_outer Z E F G F' G' p q r t y hy)]
  simp only [Linear.smul_comp, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun f => sign k (p * t) • ((reservoirShiftTripleIso Z E F G p q r).hom ≫ f))
    (reservoirTripleIso_outer (k := k) Z E F G F' G' y)

/-- Inner crossings after total removal. -/
theorem reservoirTotal_inner {a b c c' d e : B} (Z : a ⟶ b)
    (E : b ⟶ c) (F : c ⟶ d) (E' : b ⟶ c') (F' : c' ⟶ d) (G : d ⟶ e)
    (p q r t : ZMod 2) (x : E ≫ F ⟶ E' ≫ F')
    (hx : x ∈ parity (R := k) _ _ t) :
    (homParityShift (k := k) r).map
      (((homPostPairRemoval (k := k) E F p q Z).hom ≫ Z ◁ x ≫
        (homPostPairRemoval (k := k) E' F' q p Z).inv) ▷ G) ≫
      (reservoirTotalIso Z E' F' G q p r).hom =
    sign k (r * t) • ((reservoirTotalIso Z E F G p q r).hom ≫
      Z ◁ ((associator E F G).inv ≫ x ▷ G ≫ (associator E' F' G).hom)) := by
  simp only [reservoirTotalIso, Iso.trans_hom]
  rw [reassoc_of% (reservoirShiftTriple_inner Z E F E' F' G p q r t x hx)]
  simp only [Linear.smul_comp, Category.assoc]
  rw [reservoirTripleIso_inner (k := k)]

namespace ProbeReservoir

/-- The shift attached to the untouched strand gives the same sign on every edge. -/
theorem reservoir_content_sign (i j r : I) (β : I →₀ ℕ) :
    homContentShift D i β * (D.parity j * D.parity r) =
      contentParity D β * (D.parity i * D.parity j * D.parity r) := by
  unfold homContentShift
  ring

/-- The multicolour reservoir braid transported through the prescribed parity
comparisons. Intermediate factor weights may all be different. -/
theorem distinctPureReservoir_factor_braid (P : ProbeReservoir k B D Sc)
    (i j r : I) (hri_ne : r ≠ i) (β : I →₀ ℕ) {a bi bj br cij cir cjr d : X}
    (hi : a + D.α i = bi) (hj : a + D.α j = bj) (hr : a + D.α r = br)
    (hij : bi + D.α j = cij) (hji : bj + D.α i = cij)
    (hir : bi + D.α r = cir) (hri : br + D.α i = cir)
    (hjr : bj + D.α r = cjr) (hrj : br + D.α j = cjr)
    (hd12 : cij + D.α r = d) (hd13 : cir + D.α j = d)
    (hd23 : cjr + D.α i = d) {e : B} (Z : e ⟶ P.W.obj a) :
    let pi := homContentShift D i β
    let pj := homContentShift D j β
    let pr := homContentShift D r β
    (homParityShift (k := k) pr).map
      (resCore P.W j i pj pi hi hij hj hji Z ▷ P.W.E r hd12) ≫
      resCore P.W r i pr pi hji hd12 hjr hd23
        ((homParityShift (k := k) pj).obj (Z ≫ P.W.E j hj)) ≫
      (homParityShift (k := k) pi).map
        (resCore P.W r j pr pj hj hjr hr hrj Z ▷ P.W.E i hd23) =
    resCore P.W r j pr pj hij hd12 hir hd13
        ((homParityShift (k := k) pi).obj (Z ≫ P.W.E i hi)) ≫
      (homParityShift (k := k) pj).map
        (resCore P.W r i pr pi hi hir hr hri Z ▷ P.W.E j hd13) ≫
      resCore P.W j i pj pi hri hd13 hrj hd23
        ((homParityShift (k := k) pr).obj (Z ≫ P.W.E r hr)) := by
  dsimp only
  simp only [resCore_content_eq]
  apply (cancel_mono (reservoirTotalIso Z (P.W.E r hr) (P.W.E j hrj) (P.W.E i hd23)
    (homContentShift D r β) (homContentShift D j β) (homContentShift D i β)).hom).mp
  have inner := @reservoirTotal_inner k _ B _ _ _ _ _ _
  have outer := @reservoirTotal_outer k _ B _ _ _ _ _ _
  have h1 := inner Z _ _ _ _ (P.W.E r hd12)
    (homContentShift D i β) (homContentShift D j β) (homContentShift D r β) _ _
    (P.W.cross_mem j i hi hij hj hji)
  have h2 := outer Z (P.W.E j hj) _ _ _ _
    (homContentShift D j β) (homContentShift D i β) (homContentShift D r β) _ _
    (P.W.cross_mem r i hji hd12 hjr hd23)
  have h3 := inner Z _ _ _ _ (P.W.E i hd23)
    (homContentShift D j β) (homContentShift D r β) (homContentShift D i β) _ _
    (P.W.cross_mem r j hj hjr hr hrj)
  have h4 := outer Z (P.W.E i hi) _ _ _ _
    (homContentShift D i β) (homContentShift D j β) (homContentShift D r β) _ _
    (P.W.cross_mem r j hij hd12 hir hd13)
  have h5 := inner Z _ _ _ _ (P.W.E j hd13)
    (homContentShift D i β) (homContentShift D r β) (homContentShift D j β) _ _
    (P.W.cross_mem r i hi hir hr hri)
  have h6 := outer Z (P.W.E r hr) _ _ _ _
    (homContentShift D r β) (homContentShift D i β) (homContentShift D j β) _ _
    (P.W.cross_mem j i hri hd13 hrj hd23)
  simp only [Category.assoc] at h1 h2 h3 h4 h5 h6 ⊢
  rw [h3, h6]
  simp only [Linear.comp_smul]
  rw [reassoc_of% h2, reassoc_of% h5]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h4]
  simp only [Linear.smul_comp, smul_smul, Category.assoc]
  have hs (u v w : I) : homContentShift D u β * (D.parity v * D.parity w) =
      contentParity D β * (D.parity u * D.parity v * D.parity w) :=
    reservoir_content_sign u v w β
  have hb := (P.reservoirRel.braid r j i (fun h => hri_ne h.1)
    hi hj hr hij hir hji hjr hri hrj hd12 hd13 hd23).symm
  have hs1 : homContentShift D i β * (D.parity r * D.parity j) =
      homContentShift D r β * (D.parity j * D.parity i) := by rw [hs, hs]; ring
  have hs2 : homContentShift D j β * (D.parity r * D.parity i) =
      homContentShift D r β * (D.parity j * D.parity i) := by rw [hs, hs]; ring
  simp only [hs1, hs2]
  congr 2
  simpa only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc] using
    congrArg (fun f => Z ◁ f) hb

/-- The canonical all-reservoir path, with its terminal equality retained. -/
def distinctPureReservoirPath (ν : X) (i j r : I) (s : Sector I)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hr : StepValid (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)))
    {t : Sector I}
    (e : nextSector (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)) = t) :
    SPath (wd D ν [up i, up j, up r]) s t := SPath.three false false false hi hj hr e

variable (P : ProbeReservoir k B D Sc)

/-- Identification of each right edge of the all-reservoir braid. -/
theorem distinctPureReservoir_right (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (ν : X) (i j r : I) (hjr : j ≠ r) (s : Sector I)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hr : StepValid (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)))
    (hr' : StepValid (true, r) false (nextSector (true, i) false s))
    (hj' : StepValid (true, j) false (nextSector (true, r) false (nextSector (true, i) false s)))
    (e : nextSector (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)) =
      nextSector (true, j) false (nextSector (true, r) false (nextSector (true, i) false s)))
    (Z : P.H (nextSector (true, j) false (nextSector (true, r) false (nextSector (true, i) false s)))) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j r []
      (distinctPureReservoirPath ν i j r s hi hj hr e)
      (distinctPureReservoirPath ν i r j s hi hr' hj' rfl) Z)
      ((P.step (true, i) false s hi).map
        (P.postCrossNe j r (nextSector (true, i) false s) hj hr hr' hj' e Z)) := by
  dsimp only [distinctPureReservoirPath, SPath.three]
  erw [crossEntry_right]
  apply map_of_heq _ (P.pathFunctor_two_obj
    (c₁ := ⟨up j, SKM.wt D ν [up r]⟩) (c₂ := ⟨up r, SKM.wt D ν []⟩)
    (t := nextSector (true, i) false s)
    false false hj hr e Z _ (P.sector_heq e Z)) rfl
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hjr]
  exact P.twoTwo_two_heq
    ⟨up j, SKM.wt D ν [up r]⟩ ⟨up r, ν⟩
    ⟨up r, SKM.wt D ν [up j]⟩ ⟨up j, ν⟩
    (P.crossNeEntry j r _ _ _ _) (t := nextSector (true, i) false s)
    false false false false hj hr hr' hj' e rfl rfl Z Z HEq.rfl

/-- Identification of each left edge of the all-reservoir braid. The source
path is compared with the pair-tail decomposition by endpoint uniqueness. -/
theorem distinctPureReservoir_left (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (ν : X) (i j r : I) (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r) (s : Sector I)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hr : StepValid (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)))
    (hj' : StepValid (true, j) false s)
    (hi' : StepValid (true, i) false (nextSector (true, j) false s))
    (hr' : StepValid (true, r) false (nextSector (true, i) false (nextSector (true, j) false s)))
    (hs : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s))
    (e : nextSector (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)) =
      nextSector (true, r) false (nextSector (true, i) false (nextSector (true, j) false s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, i) false (nextSector (true, j) false s)))) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up r]
      (distinctPureReservoirPath ν i j r s hi hj hr e)
      (distinctPureReservoirPath ν j i r s hj' hi' hr' rfl) Z)
      (P.postCrossNe i j s hi hj hj' hi' hs
        ((P.step (true, r) false _ hr').obj Z)) := by
  let pg : SPath (wd D (SKM.wt D ν [up r]) [up i, up j]) s
      (nextSector (true, i) false (nextSector (true, j) false s)) :=
    SPath.two false false hi hj hs
  let qg : SPath (wd D (SKM.wt D ν [up r]) [up j, up i]) s
      (nextSector (true, i) false (nextSector (true, j) false s)) :=
    SPath.two false false hj' hi' rfl
  let pv : SPath (wd D ν [up r])
      (nextSector (true, i) false (nextSector (true, j) false s))
      (nextSector (true, r) false (nextSector (true, i) false (nextSector (true, j) false s))) :=
    .cons _ false _ hr' (.nil _)
  have hp : distinctPureReservoirPath (D := D) ν i j r s hi hj hr e = pg.append pv :=
    path_eq_three_distinct hij hir hjr _ _
  have hq : distinctPureReservoirPath (D := D) ν j i r s hj' hi' hr' rfl = qg.append pv := rfl
  rw [hp, hq]
  erw [crossEntry_left]
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hij]
  exact P.twoTwo_two_heq
    ⟨up i, SKM.wt D (SKM.wt D ν [up r]) [up j]⟩ ⟨up j, SKM.wt D ν [up r]⟩
    ⟨up j, SKM.wt D (SKM.wt D ν [up r]) [up i]⟩ ⟨up i, SKM.wt D ν [up r]⟩
    (P.crossNeEntry i j _ _ _ _) (t := s) false false false false
    hi hj hj' hi' hs rfl rfl _ _ HEq.rfl

/-- The left braid sum has one term for every intermediate distinct-colour
word. This applies in particular to the canonical all-reservoir paths. -/
theorem distinctPureReservoir_braidLeft_sum (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (ν : X) (i j r : I) (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    {s t : Sector I} (p : SPath (wd D ν [up i, up j, up r]) s t)
    (m₁ : SPath (wd D ν [up j, up i, up r]) s t)
    (m₂ : SPath (wd D ν [up j, up r, up i]) s t)
    (q : SPath (wd D ν [up r, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j r ν p q Z =
      (crossEntry (P.swappedGens c L) ν [] i j [up r] p m₁ Z ≫
        crossEntry (P.swappedGens c L) ν [up j] i r [] m₁ m₂ Z) ≫
        crossEntry (P.swappedGens c L) ν [] j r [up i] m₂ q Z := by
  let : Subsingleton (SPath (wd D ν [up j, up i, up r]) s t) :=
    ⟨path_eq_three_distinct hij.symm hjr hir⟩
  let : Subsingleton (SPath (wd D ν [up j, up r, up i]) s t) :=
    ⟨path_eq_three_distinct hjr hij.symm hir.symm⟩
  let : Fintype (SPath (wd D ν [up j, up i, up r]) s t) := Fintype.ofFinite _
  let : Fintype (SPath (wd D ν [up j, up r, up i]) s t) := Fintype.ofFinite _
  unfold braidLeft
  exact (Fintype.sum_subsingleton _ m₂).trans
    (congrArg (fun f => f ≫ crossEntry (P.swappedGens c L) ν [] j r [up i] m₂ q Z)
      (Fintype.sum_subsingleton _ m₁))

/-- The right braid sum has one term for every intermediate distinct-colour
word. No relation assumption is used in collapsing the sum. -/
theorem distinctPureReservoir_braidRight_sum (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (ν : X) (i j r : I) (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    {s t : Sector I} (p : SPath (wd D ν [up i, up j, up r]) s t)
    (m₁ : SPath (wd D ν [up i, up r, up j]) s t)
    (m₂ : SPath (wd D ν [up r, up i, up j]) s t)
    (q : SPath (wd D ν [up r, up j, up i]) s t) (Z : P.H t) :
    braidRight (P.swappedGens c L) i j r ν p q Z =
      (crossEntry (P.swappedGens c L) ν [up i] j r [] p m₁ Z ≫
        crossEntry (P.swappedGens c L) ν [] i r [up j] m₁ m₂ Z) ≫
        crossEntry (P.swappedGens c L) ν [up r] i j [] m₂ q Z := by
  let : Subsingleton (SPath (wd D ν [up i, up r, up j]) s t) :=
    ⟨path_eq_three_distinct hir hij hjr.symm⟩
  let : Subsingleton (SPath (wd D ν [up r, up i, up j]) s t) :=
    ⟨path_eq_three_distinct hir.symm hjr.symm hij⟩
  let : Fintype (SPath (wd D ν [up i, up r, up j]) s t) := Fintype.ofFinite _
  let : Fintype (SPath (wd D ν [up r, up i, up j]) s t) := Fintype.ofFinite _
  unfold braidRight
  exact (Fintype.sum_subsingleton _ m₂).trans
    (congrArg (fun f => f ≫ crossEntry (P.swappedGens c L) ν [up r] i j [] m₂ q Z)
      (Fintype.sum_subsingleton _ m₁))

/-- Normalize a reservoir crossing at freely chosen weight vertices. -/
theorem postCrossNe_normalized_heq (i j : I) (s : Sector I)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hj' : StepValid (true, j) false s)
    (hi' : StepValid (true, i) false (nextSector (true, j) false s))
    (hs : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s))
    (Z : P.H (nextSector (true, i) false (nextSector (true, j) false s)))
    {a b b' d : X} {v : B}
    (ha : a = P.muM (nextSector (true, j) false (nextSector (true, i) false s)))
    (hb : b = P.muM (nextSector (true, i) false s))
    (hb' : b' = P.muM (nextSector (true, j) false s)) (hd : d = P.muM s)
    (hv : v = P.T.obj (-P.muP s))
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = b') (h₄ : b' + D.α j = d)
    (Z' : v ⟶ P.W.obj a) (hZ : HEq Z Z') :
    HEq (P.postCrossNe i j s hi hj hj' hi' hs Z)
      (resCore P.W i j (homContentShift D i s.1) (homContentShift D j s.1)
        h₁ h₂ h₃ h₄ Z') := by
  subst a b b' d v
  have hz := (P.sector_heq hs Z).trans hZ
  have h := P.postCrossNe_heq i j s hi hj hj' hi' hs Z h₃
  cases hz
  exact h

/-- Evaluation of a reservoir triple with normalized weight vertices. -/
theorem distinctPureReservoir_obj (ν : X) (i j r : I) (s : Sector I)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hr : StepValid (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)))
    {t : Sector I}
    (e : nextSector (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)) = t)
    (Z : P.H t) {b d f : X} {v : B}
    (hb : b = P.muM (nextSector (true, i) false s))
    (hd : d = P.muM (nextSector (true, j) false (nextSector (true, i) false s)))
    (hf : f = P.muM t) (hv : v = P.T.obj (-P.muP t))
    (hiw : b + D.α i = P.muM s) (hjw : d + D.α j = b) (hrw : f + D.α r = d)
    (Z' : v ⟶ P.W.obj f) (hZ : HEq Z Z') :
    HEq ((P.pathFunctor (distinctPureReservoirPath (D := D) ν i j r s hi hj hr e)).obj Z)
      ((homParityShift (k := k) (homContentShift D i s.1)).obj
        ((homParityShift (k := k) (homContentShift D j s.1)).obj
          ((homParityShift (k := k) (homContentShift D r s.1)).obj
            (Z' ≫ P.W.E r hrw) ≫ P.W.E j hjw) ≫ P.W.E i hiw)) := by
  subst e b d f v
  cases hZ
  rfl

/-- Evaluation of a reservoir step with normalized vertices. -/
theorem reservoirStep_obj_normalized (i : I) (s : Sector I)
    (hi : StepValid (true, i) false s) {t : Sector I}
    (e : nextSector (true, i) false s = t) (Z : P.H t)
    {a b : X} {v : B} (ha : a = P.muM t) (hb : b = P.muM s)
    (hv : v = P.T.obj (-P.muP t)) (hiw : a + D.α i = b)
    (Z' : v ⟶ P.W.obj a) (hZ : HEq Z Z') :
    HEq ((P.step (true, i) false s hi).obj (e ▸ Z))
      ((homParityShift (k := k) (homContentShift D i s.1)).obj (Z' ≫ P.W.E i hiw)) := by
  subst e a b v
  cases hZ
  rfl

/-- Evaluation of two reservoir steps with normalized vertices. -/
theorem reservoirPair_obj_normalized (i j : I) (s : Sector I)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s)) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false s) = t) (Z : P.H t)
    {a b d : X} {v : B} (ha : a = P.muM t)
    (hb : b = P.muM (nextSector (true, i) false s)) (hd : d = P.muM s)
    (hv : v = P.T.obj (-P.muP t)) (hiw : b + D.α i = d) (hjw : a + D.α j = b)
    (Z' : v ⟶ P.W.obj a) (hZ : HEq Z Z') :
    HEq ((P.step (true, i) false s hi).obj
      ((P.step (true, j) false _ hj).obj (e ▸ Z)))
      ((homParityShift (k := k) (homContentShift D i s.1)).obj
        ((homParityShift (k := k) (homContentShift D j s.1)).obj
          (Z' ≫ P.W.E j hjw) ≫ P.W.E i hiw)) := by
  subst e a b d v
  cases hZ
  rfl

/-- The left all-reservoir edge in common factor coordinates. -/
theorem distinctPureReservoir_left_core (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hr : StepValid (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)))
    (hj' : StepValid (true, j) false s)
    (hi' : StepValid (true, i) false (nextSector (true, j) false s))
    (hr' : StepValid (true, r) false (nextSector (true, i) false (nextSector (true, j) false s)))
    (hs : nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s)) {t : Sector I}
    (e : nextSector (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)) = t)
    (e' : nextSector (true, r) false (nextSector (true, i) false (nextSector (true, j) false s)) = t)
    (Z : P.H t) {b b' d f : X}
    (hb : b = P.muM (nextSector (true, i) false s))
    (hb' : b' = P.muM (nextSector (true, j) false s))
    (hd : d = P.muM (nextSector (true, j) false (nextSector (true, i) false s)))
    (hf : f = P.muM t)
    (hiw : b + D.α i = P.muM s) (hjw : d + D.α j = b)
    (hjw' : b' + D.α j = P.muM s) (hiw' : d + D.α i = b')
    (hrw : f + D.α r = d) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up r]
      (distinctPureReservoirPath ν i j r s hi hj hr e)
      (distinctPureReservoirPath ν j i r s hj' hi' hr' e') Z)
      (resCore P.W i j (homContentShift D i s.1) (homContentShift D j s.1)
        hjw hiw hiw' hjw'
        ((homParityShift (k := k) (homContentShift D r s.1)).obj
          ((hf ▸ Z : P.T.obj (-P.muP t) ⟶ P.W.obj f) ≫ P.W.E r hrw))) := by
  subst e'
  refine (P.distinctPureReservoir_left c L ν i j r hij hir hjr s
    hi hj hr hj' hi' hr' hs e Z).trans ?_
  exact P.postCrossNe_normalized_heq i j s hi hj hj' hi' hs _ hd hb hb' rfl rfl
    hjw hiw hiw' hjw' _
    (P.reservoirStep_obj_normalized r _ hr' rfl Z hf
      (hd.trans (congrArg P.muM hs)) rfl hrw _ (by subst f; rfl))

/-- The right all-reservoir edge in common factor coordinates. -/
theorem distinctPureReservoir_right_core (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hjr : j ≠ r)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hr : StepValid (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)))
    (hr' : StepValid (true, r) false (nextSector (true, i) false s))
    (hj' : StepValid (true, j) false (nextSector (true, r) false (nextSector (true, i) false s)))
    {t : Sector I}
    (e : nextSector (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)) = t)
    (e' : nextSector (true, j) false (nextSector (true, r) false (nextSector (true, i) false s)) = t)
    (Z : P.H t) {b d d' f : X}
    (hb : b = P.muM (nextSector (true, i) false s))
    (hd : d = P.muM (nextSector (true, j) false (nextSector (true, i) false s)))
    (hd' : d' = P.muM (nextSector (true, r) false (nextSector (true, i) false s)))
    (hf : f = P.muM t)
    (hiw : b + D.α i = P.muM s) (hjw : d + D.α j = b) (hrw : d' + D.α r = b)
    (hrw' : f + D.α r = d) (hjw' : f + D.α j = d') :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j r []
      (distinctPureReservoirPath ν i j r s hi hj hr e)
      (distinctPureReservoirPath ν i r j s hi hr' hj' e') Z)
      ((homParityShift (k := k) (homContentShift D i s.1)).map
        (resCore P.W j r (homContentShift D j s.1) (homContentShift D r s.1)
          hrw' hjw hjw' hrw (hf ▸ Z : P.T.obj (-P.muP t) ⟶ P.W.obj f) ▷ P.W.E i hiw)) := by
  subst e' b f
  refine (P.distinctPureReservoir_right c L ν i j r hjr s hi hj hr hr' hj' e Z).trans ?_
  have hA := P.reservoirPair_obj_normalized j r (nextSector (true, i) false s)
    hj hr e Z rfl hd rfl rfl hjw hrw' Z HEq.rfl
  have hB := P.reservoirPair_obj_normalized r j (nextSector (true, i) false s)
    hr' hj' rfl Z rfl hd' rfl rfl hrw hjw' Z HEq.rfl
  exact map_of_heq (P.step (true, i) false s hi) (eq_of_heq hA) (eq_of_heq hB)
    (P.postCrossNe_normalized_heq j r (nextSector (true, i) false s) hj hr hr' hj' e Z
      (congrArg P.muM e.symm) hd hd' rfl rfl hrw' hjw hjw' hrw Z HEq.rfl)

/-- Reservoir decrements commute, including truncated content subtraction. -/
theorem pureReservoir_swap (i j : I) (s : Sector I) :
    nextSector (true, j) false (nextSector (true, i) false s) =
      nextSector (true, i) false (nextSector (true, j) false s) := by
  simp only [nextSector, tsub_right_comm]

/-- Removing a different colour preserves the validity of a reservoir step. -/
theorem pureReservoir_valid_iff (i j : I) (hij : i ≠ j) (s : Sector I) :
    StepValid (true, j) false (nextSector (true, i) false s) ↔
      StepValid (true, j) false s := by
  simp [StepValid, nextSector, hij.symm]

/-- The canonical all-reservoir sector of the pairwise-distinct braid relation.
The supplied reservoir braid is transported through all six actual crossing
entries, including their content-dependent parity shifts. -/
theorem distinctPureReservoir_braid (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hr : StepValid (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)))
    (hr' : StepValid (true, r) false s)
    (hj' : StepValid (true, j) false (nextSector (true, r) false s))
    (hi' : StepValid (true, i) false (nextSector (true, j) false (nextSector (true, r) false s)))
    {t : Sector I}
    (e : nextSector (true, r) false (nextSector (true, j) false (nextSector (true, i) false s)) = t)
    (e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, r) false s)) = t)
    (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j r ν
      (distinctPureReservoirPath ν i j r s hi hj hr e)
      (distinctPureReservoirPath ν r j i s hr' hj' hi' e') Z =
    braidRight (P.swappedGens c L) i j r ν
      (distinctPureReservoirPath ν i j r s hi hj hr e)
      (distinctPureReservoirPath ν r j i s hr' hj' hi' e') Z := by
  classical
  subst e'
  let t := nextSector (true, i) false (nextSector (true, j) false (nextSector (true, r) false s))
  have vj := (pureReservoir_valid_iff i j hij s).mp hj
  have vji := (pureReservoir_valid_iff j i hij.symm s).mpr hi
  have vir := (pureReservoir_valid_iff i r hir s).mpr hr'
  have vjr := (pureReservoir_valid_iff j r hjr s).mpr hr'
  have vri := (pureReservoir_valid_iff r i hir.symm s).mpr hi
  have vjir := (pureReservoir_valid_iff i r hir _).mpr vjr
  have vjri := (pureReservoir_valid_iff r i hir.symm _).mpr vji
  have virj := (pureReservoir_valid_iff r j hjr.symm _).mpr hj
  have vrij := (pureReservoir_valid_iff i j hij _).mpr hj'
  have e213 : nextSector (true, r) false (nextSector (true, i) false (nextSector (true, j) false s)) = t :=
    (congrArg (nextSector (true, r) false) (pureReservoir_swap j i s)).trans e
  have e231 : nextSector (true, i) false (nextSector (true, r) false (nextSector (true, j) false s)) = t :=
    (pureReservoir_swap r i _).trans e213
  have e132 : nextSector (true, j) false (nextSector (true, r) false (nextSector (true, i) false s)) = t :=
    (pureReservoir_swap r j _).trans e
  have e312 : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, r) false s)) = t :=
    (pureReservoir_swap i j _).trans rfl
  rw [P.distinctPureReservoir_braidLeft_sum c L ν i j r hij hir hjr _
    (distinctPureReservoirPath ν j i r s vj vji vjir e213)
    (distinctPureReservoirPath ν j r i s vj vjr vjri e231),
    P.distinctPureReservoir_braidRight_sum c L ν i j r hij hir hjr _
    (distinctPureReservoirPath ν i r j s hi vir virj e132)
    (distinctPureReservoirPath ν r i j s hr' vri vrij e312)]
  have wji := congrArg P.muM (pureReservoir_swap i j s)
  have wri := congrArg P.muM (pureReservoir_swap i r s)
  have wrj := congrArg P.muM (pureReservoir_swap j r s)
  have hji : P.muM (nextSector (true, j) false (nextSector (true, i) false s)) + D.α i =
      P.muM (nextSector (true, j) false s) := by
    rw [wji]; exact P.muM_postE i vji
  have hri : P.muM (nextSector (true, r) false (nextSector (true, i) false s)) + D.α i =
      P.muM (nextSector (true, r) false s) := by
    rw [wri]; exact P.muM_postE i vri
  have hrj : P.muM (nextSector (true, r) false (nextSector (true, j) false s)) + D.α j =
      P.muM (nextSector (true, r) false s) := by
    rw [wrj]; exact P.muM_postE j hj'
  have hd12 : P.muM t + D.α r =
      P.muM (nextSector (true, j) false (nextSector (true, i) false s)) := by
    dsimp only [t]
    rw [← e]; exact P.muM_postE r hr
  have hd13 : P.muM t + D.α j =
      P.muM (nextSector (true, r) false (nextSector (true, i) false s)) := by
    rw [← e132]; exact P.muM_postE j virj
  have hd23 : P.muM t + D.α i =
      P.muM (nextSector (true, r) false (nextSector (true, j) false s)) := by
    rw [← e231]; exact P.muM_postE i vjri
  exact probeHexagon_of_heq
    (eq_of_heq (P.distinctPureReservoir_obj ν i j r s hi hj hr e Z rfl rfl rfl rfl
      (P.muM_postE i hi) (P.muM_postE j hj) hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν j i r s vj vji vjir e213 Z rfl wji rfl rfl
      (P.muM_postE j vj) hji hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν j r i s vj vjr vjri e231 Z rfl rfl rfl rfl
      (P.muM_postE j vj) (P.muM_postE r vjr) hd23 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν r j i s hr' hj' hi' rfl Z rfl wrj rfl rfl
      (P.muM_postE r hr') hrj hd23 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν i r j s hi vir virj e132 Z rfl rfl rfl rfl
      (P.muM_postE i hi) (P.muM_postE r vir) hd13 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν r i j s hr' vri vrij e312 Z rfl wri rfl rfl
      (P.muM_postE r hr') hri hd13 Z HEq.rfl))
    (P.distinctPureReservoir_left_core ν i j r s c L hij hir hjr hi hj hr vj vji vjir
      (pureReservoir_swap i j s) e e213 Z rfl rfl rfl rfl
      (P.muM_postE i hi) (P.muM_postE j hj) (P.muM_postE j vj) hji hd12)
    (P.distinctPureReservoir_right_core ν j i r s c L hir vj vji vjir vjr vjri e213 e231 Z
      rfl wji rfl rfl (P.muM_postE j vj) hji (P.muM_postE r vjr) hd12 hd23)
    (P.distinctPureReservoir_left_core ν j r i s c L hjr hij.symm hir.symm
      vj vjr vjri hr' hj' hi' (pureReservoir_swap j r s) e231 rfl Z rfl rfl rfl rfl
      (P.muM_postE j vj) (P.muM_postE r vjr) (P.muM_postE r hr') hrj hd23)
    (P.distinctPureReservoir_right_core ν i j r s c L hjr hi hj hr vir virj e e132 Z
      rfl rfl rfl rfl (P.muM_postE i hi) (P.muM_postE j hj) (P.muM_postE r vir) hd12 hd13)
    (P.distinctPureReservoir_left_core ν i r j s c L hir hij hjr.symm hi vir virj hr' vri vrij
      (pureReservoir_swap i r s) e132 e312 Z rfl rfl rfl rfl
      (P.muM_postE i hi) (P.muM_postE r vir) (P.muM_postE r hr') hri hd13)
    (P.distinctPureReservoir_right_core ν r i j s c L hij hr' vri vrij hj' hi' e312 rfl Z
      rfl wri wrj rfl (P.muM_postE r hr') hri hrj hd13 hd23)
    (P.distinctPureReservoir_factor_braid r j i hir s.1 hd12 hd13 hd23
      (P.muM_postE j hj) (P.muM_postE r vir) hji (P.muM_postE r vjr) hri hrj
      (P.muM_postE i hi) (P.muM_postE j vj) (P.muM_postE r hr') Z).symm

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
