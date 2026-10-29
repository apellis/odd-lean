/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SlideSame

/-! # The distinct-colour slide relations for the swapped crossing

The relations `slideL` and `slideR` of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, (1.8), on `Eᵢ Eⱼ` with `i ≠ j`, for the image `crossImage` of the upward
crossing in the swapped action (`docs/Nondegeneracy/SwappedActionAssembly.md`, §3).
-/

noncomputable section

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

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- A whiskered 2-morphism commutes with the transport along an equality of composites,
for heterogeneously equal data. -/
theorem whiskerRight_eqToHom_heq {a b b' c : B} (hb : b = b') {E : a ⟶ b} {E' : a ⟶ b'}
    (hE : HEq E E') {Z : b ⟶ c} {Z' : b' ⟶ c} (hZ : HEq Z Z') {x : E ⟶ E} {x' : E' ⟶ E'}
    (hx : HEq x x') (e : E ≫ Z = E' ≫ Z') :
    x ▷ Z ≫ eqToHom e = eqToHom e ≫ x' ▷ Z' := by
  subst hb
  cases hE
  cases hZ
  cases hx
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

section Abstract

omit [∀ a b : B, PiSupercategory k (a ⟶ b)]

variable {a b b' c d e' : B} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {E₂' : a ⟶ b'} {E₁' : b' ⟶ c}
  {Z₀ : c ⟶ d} {W : b' ⟶ d}

/-- The left slide through a reassociated crossing followed by a map on the outer factor. -/
theorem conj_cross_slideL (x : E₁ ⟶ E₁) (x' : E₁' ⟶ E₁') (t : E₁ ≫ E₂ ⟶ E₂' ≫ E₁')
    (f : E₁' ≫ Z₀ ⟶ W) (y : W ⟶ W) (z : k) (hS : x ▷ E₂ ≫ t = z • (t ≫ E₂' ◁ x'))
    (hf : x' ▷ Z₀ ≫ f = f ≫ y) :
    x ▷ (E₂ ≫ Z₀) ≫ (associator E₁ E₂ Z₀).inv ≫ t ▷ Z₀ ≫ (associator E₂' E₁' Z₀).hom ≫
        E₂' ◁ f =
      z • (((associator E₁ E₂ Z₀).inv ≫ t ▷ Z₀ ≫ (associator E₂' E₁' Z₀).hom ≫ E₂' ◁ f) ≫
        E₂' ◁ y) := by
  rw [TwoSupercategory.whiskerRight_comp (R := k)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h1 : x ▷ E₂ ▷ Z₀ ≫ t ▷ Z₀ = z • (t ▷ Z₀ ≫ (E₂' ◁ x') ▷ Z₀) := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), hS,
      TwoSupercategory.smul_whiskerRight (R := k), TwoSupercategory.comp_whiskerRight (R := k)]
  rw [reassoc_of% h1, TwoSupercategory.whisker_assoc (R := k)]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← TwoSupercategory.whiskerLeft_comp (R := k), hf,
    TwoSupercategory.whiskerLeft_comp (R := k)]

/-- The right slide through a reassociated crossing followed by a map on the outer factor. -/
theorem conj_cross_slideR (x₂ : E₂ ⟶ E₂) (x₂' : E₂' ⟶ E₂') (t : E₁ ≫ E₂ ⟶ E₂' ≫ E₁')
    (f : E₁' ≫ Z₀ ⟶ W) (z : k) {p : ZMod 2} (hx : x₂' ∈ parity (R := k) _ _ p)
    (hf : f ∈ parity (R := k) _ _ 0) (hS : t ≫ x₂' ▷ E₁' = z • (E₁ ◁ x₂ ≫ t)) :
    ((associator E₁ E₂ Z₀).inv ≫ t ▷ Z₀ ≫ (associator E₂' E₁' Z₀).hom ≫ E₂' ◁ f) ≫
        x₂' ▷ W =
      z • (E₁ ◁ (x₂ ▷ Z₀) ≫
        (associator E₁ E₂ Z₀).inv ≫ t ▷ Z₀ ≫ (associator E₂' E₁' Z₀).hom ≫ E₂' ◁ f) := by
  have hx' := TwoSupercategory.super_interchange (R := k) hx hf
  rw [koszulSign_zero_right, one_smul] at hx'
  have h1 : t ▷ Z₀ ≫ (x₂' ▷ E₁') ▷ Z₀ = z • ((E₁ ◁ x₂) ▷ Z₀ ≫ t ▷ Z₀) := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), hS,
      TwoSupercategory.smul_whiskerRight (R := k), TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [Category.assoc]
  rw [← hx', TwoSupercategory.whiskerRight_comp (R := k)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h1, TwoSupercategory.whisker_assoc (R := k)]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc, Iso.inv_hom_id_assoc]

end Abstract

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] [TwoSupercategory k B] in
theorem eqToHom_mem_zero {a b : B} {f g : a ⟶ b} (e : f = g) :
    eqToHom e ∈ parity (R := k) f g 0 := by
  subst e
  exact id_mem _

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] [TwoSupercategory k B] in
theorem zsign_mul_self' (p : ZMod 2) : zsign k p * zsign k p = 1 := by
  unfold zsign
  split_ifs <;> simp

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] [TwoSupercategory k B] in
theorem sector_heq {s s' : Sector I} (hs : s = s') (Z : P.H s') : HEq (hs ▸ Z : P.H s) Z := by
  subst hs
  rfl

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] [TwoSupercategory k B] in
theorem probeE_heq (i : I) {x y y' : X} (hy : y = y') (h : x + D.α i = y)
    (h' : x + D.α i = y') : HEq (P.T.E i h) (P.T.E i h') := by
  subst hy
  rfl

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] [TwoSupercategory k B] in
theorem probeDot_heq (i : I) {x y y' : X} (hy : y = y') (h : x + D.α i = y)
    (h' : x + D.α i = y') : HEq (P.T.dot i h) (P.T.dot i h') := by
  subst hy
  rfl

theorem preCrossNe_slideL (i j : I) (hij : i ≠ j) (t : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true t) =
      nextSector (true, i) true (nextSector (true, j) true t))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true t))) :
    (P.T.dot i (P.muP_preE i t) ▷ (P.step (true, j) true _ trivial).obj (hs ▸ Z)) ≫
        P.preCrossNe i j t hs Z =
      zsign k (D.parity i * D.parity j) • (P.preCrossNe i j t hs Z ≫
        (P.step (true, j) true t trivial).map (P.T.dot i (P.muP_preE i _) ▷ Z)) := by
  have hS := (P.probeRel.slideRight j i hij.symm (P.muP_preE i t) (P.muP_preE j _)
    (P.muP_preE j t) (by rw [hs]; exact P.muP_preE i _))
  rw [mul_comm] at hS
  have hy : -P.muP (nextSector (true, j) true (nextSector (true, i) true t)) =
      -P.muP (nextSector (true, i) true (nextSector (true, j) true t)) := by rw [hs]
  exact conj_cross_slideL (k := k) _ _ _ _ _ _ (by rw [hS, smul_smul, zsign_mul_self', one_smul])
    (whiskerRight_eqToHom_heq (congrArg P.T.obj hy) (P.probeE_heq i hy _ _) (P.sector_heq hs Z)
      (P.probeDot_heq i hy _ _) _)

theorem preCrossNe_slideR (i j : I) (hij : i ≠ j) (t : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true t) =
      nextSector (true, i) true (nextSector (true, j) true t))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true t))) :
    P.preCrossNe i j t hs Z ≫
        (P.T.dot j (P.muP_preE j t) ▷ (P.step (true, i) true _ trivial).obj Z) =
      zsign k (D.parity i * D.parity j) • ((P.step (true, i) true t trivial).map
        (P.T.dot j _ ▷ (hs ▸ Z)) ≫ P.preCrossNe i j t hs Z) := by
  have hS := (P.probeRel.slideLeft j i hij.symm (P.muP_preE i t) (P.muP_preE j _)
    (P.muP_preE j t) (by rw [hs]; exact P.muP_preE i _))
  rw [mul_comm] at hS
  exact conj_cross_slideR (k := k) _ _ _ _ _ (P.T.dot_mem j _) (eqToHom_mem_zero _)
    (by rw [hS, smul_smul, zsign_mul_self', one_smul])

/-! ## The reservoir/reservoir entry -/

section PostAbstract

variable {x a b c b' : B} (Z : x ⟶ a) (Ej : a ⟶ b) (Ei : b ⟶ c) {Ei' : a ⟶ b'} {Ej' : b' ⟶ c}

/-- A homogeneous 2-morphism on the outer letter moves across `postPairIso` without sign. -/
theorem postPairIso_outer (κi κj : ZMod 2) (xi : Ei ⟶ Ei) {p : ZMod 2}
    (hx : xi ∈ parity (R := k) _ _ p) :
    (homParityShift (k := k) κi).map ((homParityShift (k := k) κj).obj (Z ≫ Ej) ◁ xi) ≫
        (postPairIso (k := k) Ei Z Ej κi κj).hom =
      (postPairIso (k := k) Ei Z Ej κi κj).hom ≫
        (homParityShift (k := k) (κj + κi)).map ((Z ≫ Ej) ◁ xi) := by
  have hc := homParityShiftCommute_supernatural (k := k) (homPost (k := k) (a := x) Ei)
    (homPost (k := k) Ei) κj p _ ((homPostTransform xi hx).isSupernatural p) (Z ≫ Ej)
  simp only [homPostTransform, ↓reduceIte] at hc
  have hc' : (homParityShift (k := k) κj).obj (Z ≫ Ej) ◁ xi ≫
      (homParityShiftCommute (k := k) (homPost (k := k) Ei) κj).inv.app (Z ≫ Ej) =
      (homParityShiftCommute (k := k) (homPost (k := k) Ei) κj).inv.app (Z ≫ Ej) ≫
        (homParityShift (k := k) κj).map ((Z ≫ Ej) ◁ xi) := by
    rw [← cancel_epi ((homParityShiftCommute (k := k) (homPost (k := k) Ei) κj).hom.app
      (Z ≫ Ej)), Iso.hom_inv_id_app_assoc, ← Category.assoc]
    erw [← hc]
    rw [Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  simp only [postPairIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, hc', Functor.map_comp, Category.assoc]
  congr 1
  exact (homParityShiftAdd (k := k) κj κi).hom.naturality ((Z ≫ Ej) ◁ xi)

/-- The outer-letter transport, for the inverse comparison. -/
theorem postPairIso_outer_inv (κi κj : ZMod 2) (xi : Ei ⟶ Ei) {p : ZMod 2}
    (hx : xi ∈ parity (R := k) _ _ p) :
    (homParityShift (k := k) (κj + κi)).map ((Z ≫ Ej) ◁ xi) ≫
        (postPairIso (k := k) Ei Z Ej κi κj).inv =
      (postPairIso (k := k) Ei Z Ej κi κj).inv ≫
        (homParityShift (k := k) κi).map ((homParityShift (k := k) κj).obj (Z ≫ Ej) ◁ xi) := by
  rw [Iso.comp_inv_eq, Category.assoc, postPairIso_outer Z Ej Ei κi κj xi hx,
    Iso.inv_hom_id_assoc]

/-- A 2-morphism on the inner composite moves across `postPairIso` without sign. -/
theorem postPairIso_inner (κi κj : ZMod 2) (g : Z ≫ Ej ⟶ Z ≫ Ej) :
    (homParityShift (k := k) κi).map ((homParityShift (k := k) κj).map g ▷ Ei) ≫
        (postPairIso (k := k) Ei Z Ej κi κj).hom =
      (postPairIso (k := k) Ei Z Ej κi κj).hom ≫
        (homParityShift (k := k) (κj + κi)).map (g ▷ Ei) := by
  simp only [postPairIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  have hn := (homParityShiftCommute (k := k) (homPost (k := k) (a := x) Ei) κj).inv.naturality g
  erw [hn]
  rw [Functor.map_comp, Category.assoc]
  congr 1
  exact (homParityShiftAdd (k := k) κj κi).hom.naturality (g ▷ Ei)

/-- The inner-composite transport, for the inverse comparison. -/
theorem postPairIso_inner_inv (κi κj : ZMod 2) (g : Z ≫ Ej ⟶ Z ≫ Ej) :
    (homParityShift (k := k) (κj + κi)).map (g ▷ Ei) ≫
        (postPairIso (k := k) Ei Z Ej κi κj).inv =
      (postPairIso (k := k) Ei Z Ej κi κj).inv ≫
        (homParityShift (k := k) κi).map ((homParityShift (k := k) κj).map g ▷ Ei) := by
  rw [Iso.comp_inv_eq, Category.assoc, postPairIso_inner Z Ej Ei κi κj g,
    Iso.inv_hom_id_assoc]

omit [TwoSupercategory k B] in
/-- A parity shift commutes with the transport along an equality of parities. -/
theorem homParityShift_map_eqToHom {y z : B} {p q : ZMod 2} (hpq : p = q) {Y : y ⟶ z}
    (g : Y ⟶ Y) (e : (homParityShift (k := k) p).obj Y = (homParityShift (k := k) q).obj Y) :
    (homParityShift (k := k) p).map g ≫ eqToHom e =
      eqToHom e ≫ (homParityShift (k := k) q).map g := by
  subst hpq
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The left slide of a reassociated whiskered crossing. -/
theorem post_core_slideL (xi : Ei ⟶ Ei) (xi' : Ei' ⟶ Ei') (t : Ej ≫ Ei ⟶ Ei' ≫ Ej') (z : k)
    (hS : Ej ◁ xi ≫ t = z • (t ≫ xi' ▷ Ej')) :
    (Z ≫ Ej) ◁ xi ≫ (associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv =
      z • (((associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv) ≫
        (Z ◁ xi') ▷ Ej') := by
  have hm : Z ◁ (xi' ▷ Ej') ≫ (associator Z Ei' Ej').inv =
      (associator Z Ei' Ej').inv ≫ (Z ◁ xi') ▷ Ej' := by
    rw [Iso.comp_inv_eq, Category.assoc,
      TwoSupercategory.associator_naturality_middle (R := k), Iso.inv_hom_id_assoc]
  rw [TwoSupercategory.associator_naturality_right_assoc (R := k), ← Category.assoc (Z ◁ Ej ◁ xi),
    ← TwoSupercategory.whiskerLeft_comp (R := k), hS, TwoSupercategory.whiskerLeft_smul (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k)]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc, hm]

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The right slide of a reassociated whiskered crossing. -/
theorem post_core_slideR (xj : Ej ⟶ Ej) (xj' : Ej' ⟶ Ej') (t : Ej ≫ Ei ⟶ Ei' ≫ Ej') (z : k)
    (hS : t ≫ Ei' ◁ xj' = z • (xj ▷ Ei ≫ t)) :
    ((associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv) ≫ (Z ≫ Ei') ◁ xj' =
      z • ((Z ◁ xj) ▷ Ei ≫ (associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv) := by
  have hm : (associator Z Ei' Ej').inv ≫ (Z ≫ Ei') ◁ xj' =
      Z ◁ (Ei' ◁ xj') ≫ (associator Z Ei' Ej').inv := by
    rw [Iso.eq_comp_inv, Category.assoc,
      TwoSupercategory.associator_naturality_right (R := k), Iso.inv_hom_id_assoc]
  simp only [Category.assoc, hm]
  rw [← Category.assoc (Z ◁ t), ← TwoSupercategory.whiskerLeft_comp (R := k), hS,
    TwoSupercategory.whiskerLeft_smul (R := k), TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.associator_naturality_middle_assoc (R := k)]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- The left slide through the conjugated crossing of the reservoir/reservoir entry. -/
theorem conj_post_slideL (κi κj : ZMod 2) (xi : Ei ⟶ Ei) (xi' : Ei' ⟶ Ei') {p : ZMod 2}
    (hx : xi ∈ parity (R := k) _ _ p) (t : Ej ≫ Ei ⟶ Ei' ≫ Ej') (z : k)
    (hS : Ej ◁ xi ≫ t = z • (t ≫ xi' ▷ Ej'))
    (e : (homParityShift (k := k) (κj + κi)).obj ((Z ≫ Ei') ≫ Ej') =
      (homParityShift (k := k) (κi + κj)).obj ((Z ≫ Ei') ≫ Ej'))
    {Q : x ⟶ c} (f : (homParityShift (k := k) κj).obj
      ((homParityShift (k := k) κi).obj (Z ≫ Ei') ≫ Ej') ⟶ Q) (g : Q ⟶ Q)
    (hf : (homParityShift (k := k) κj).map ((homParityShift (k := k) κi).map (Z ◁ xi') ▷ Ej') ≫
      f = f ≫ g) :
    (homParityShift (k := k) κi).map ((homParityShift (k := k) κj).obj (Z ≫ Ej) ◁ xi) ≫
        (postPairIso (k := k) Ei Z Ej κi κj).hom ≫
        (homParityShift (k := k) (κj + κi)).map
          ((associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv) ≫
        eqToHom e ≫ (postPairIso (k := k) Ej' Z Ei' κj κi).inv ≫ f =
      z • (((postPairIso (k := k) Ei Z Ej κi κj).hom ≫
        (homParityShift (k := k) (κj + κi)).map
          ((associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv) ≫
        eqToHom e ≫ (postPairIso (k := k) Ej' Z Ei' κj κi).inv ≫ f) ≫ g) := by
  rw [← Category.assoc, postPairIso_outer Z Ej Ei κi κj xi hx, Category.assoc,
    ← Functor.map_comp_assoc, post_core_slideL Z Ej Ei xi xi' t z hS, Functor.map_smul,
    Functor.map_comp]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [reassoc_of% (homParityShift_map_eqToHom (add_comm κj κi) ((Z ◁ xi') ▷ Ej') e),
    reassoc_of% (postPairIso_inner_inv Z Ei' Ej' κj κi (Z ◁ xi')), hf]

/-- The right slide through the conjugated crossing of the reservoir/reservoir entry. -/
theorem conj_post_slideR (κi κj : ZMod 2) (xj : Ej ⟶ Ej) (xj' : Ej' ⟶ Ej') {p : ZMod 2}
    (hx : xj' ∈ parity (R := k) _ _ p) (t : Ej ≫ Ei ⟶ Ei' ≫ Ej') (z : k)
    (hS : t ≫ Ei' ◁ xj' = z • (xj ▷ Ei ≫ t))
    (e : (homParityShift (k := k) (κj + κi)).obj ((Z ≫ Ei') ≫ Ej') =
      (homParityShift (k := k) (κi + κj)).obj ((Z ≫ Ei') ≫ Ej'))
    {Q : x ⟶ c} (f : (homParityShift (k := k) κj).obj
      ((homParityShift (k := k) κi).obj (Z ≫ Ei') ≫ Ej') ⟶ Q) (y : Q ⟶ Q)
    (hf : (homParityShift (k := k) κj).map
      ((homParityShift (k := k) κi).obj (Z ≫ Ei') ◁ xj') ≫ f = f ≫ y) :
    ((postPairIso (k := k) Ei Z Ej κi κj).hom ≫
        (homParityShift (k := k) (κj + κi)).map
          ((associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv) ≫
        eqToHom e ≫ (postPairIso (k := k) Ej' Z Ei' κj κi).inv ≫ f) ≫ y =
      z • ((homParityShift (k := k) κi).map ((homParityShift (k := k) κj).map (Z ◁ xj) ▷ Ei) ≫
        (postPairIso (k := k) Ei Z Ej κi κj).hom ≫
        (homParityShift (k := k) (κj + κi)).map
          ((associator Z Ej Ei).hom ≫ Z ◁ t ≫ (associator Z Ei' Ej').inv) ≫
        eqToHom e ≫ (postPairIso (k := k) Ej' Z Ei' κj κi).inv ≫ f) := by
  simp only [Category.assoc]
  rw [← hf, ← reassoc_of% (postPairIso_outer_inv Z Ei' Ej' κj κi xj' hx),
    ← reassoc_of% (homParityShift_map_eqToHom (add_comm κj κi) ((Z ≫ Ei') ◁ xj') e),
    ← Functor.map_comp_assoc, post_core_slideR Z Ej Ei xj xj' t z hS, Functor.map_smul, Functor.map_comp]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [← reassoc_of% (postPairIso_inner Z Ej Ei κi κj (Z ◁ xj))]

end PostAbstract

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- An endomorphism commutes with the transport along an equality of objects, for
heterogeneously equal endomorphisms. -/
theorem end_eqToHom_heq {C : Type*} [Category C] {A A' : C} (e : A = A') {x : A ⟶ A}
    {x' : A' ⟶ A'} (hx : HEq x x') : x ≫ eqToHom e = eqToHom e ≫ x' := by
  subst e
  obtain rfl := eq_of_heq hx
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

theorem postDot_heq (i : I) (β : I →₀ ℕ) {s s' : Sector I} (hs : s = s') {x : X}
    (h : P.muM s + D.α i = x) (h' : P.muM s' + D.α i = x) (Z : P.H s') :
    HEq (homContentPostDot P.T.obj P.W i β (P.muP s) h (hs ▸ Z : P.H s))
      (homContentPostDot P.T.obj P.W i β (P.muP s') h' Z) := by
  subst hs
  rfl

theorem postCrossNe_slideL (i j : I) (hij : i ≠ j) (t : Sector I)
    (hv₁ : StepValid (true, i) false t)
    (hv₂ : StepValid (true, j) false (nextSector (true, i) false t))
    (hw₁ : StepValid (true, j) false t)
    (hw₂ : StepValid (true, i) false (nextSector (true, j) false t))
    (hs : nextSector (true, j) false (nextSector (true, i) false t) =
      nextSector (true, i) false (nextSector (true, j) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, j) false t))) :
    homContentPostDot P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv₁)
        ((P.step (true, j) false _ hv₂).obj (hs ▸ Z)) ≫
        P.postCrossNe i j t hv₁ hv₂ hw₁ hw₂ hs Z =
      zsign k (D.parity i * D.parity j) • (P.postCrossNe i j t hv₁ hv₂ hw₁ hw₂ hs Z ≫
        (P.step (true, j) false t hw₁).map (homContentPostDot P.T.obj P.W i
          (nextSector (true, j) false t).1 (P.muP _) (P.muM_postE i hw₂) Z)) := by
  have h₃ : P.muM (nextSector (true, j) false (nextSector (true, i) false t)) + D.α i =
      P.muM (nextSector (true, j) false t) := by
    rw [hs]; exact P.muM_postE i hw₂
  have hS := P.reservoirRel.slideLeft i j hij (P.muM_postE j hv₂) (P.muM_postE i hv₁) h₃
    (P.muM_postE j hw₁)
  have hf : (P.step (true, j) false t hw₁).map
        (homContentPostDot P.T.obj P.W i t.1 (P.muP _) h₃ (hs ▸ Z : P.H (nextSector (true, j) false (nextSector (true, i) false t)))) ≫
        (P.step (true, j) false t hw₁).map
          (eqToHom (eq_of_heq (P.postE_obj_heq i t.1 hs h₃ (P.muM_postE i hw₂) Z))) =
      (P.step (true, j) false t hw₁).map
          (eqToHom (eq_of_heq (P.postE_obj_heq i t.1 hs h₃ (P.muM_postE i hw₂) Z))) ≫
        (P.step (true, j) false t hw₁).map (homContentPostDot P.T.obj P.W i
          (nextSector (true, j) false t).1 (P.muP _) (P.muM_postE i hw₂) Z) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      end_eqToHom_heq _ (P.postDot_heq i t.1 hs h₃ (P.muM_postE i hw₂) Z)]
    rfl
  exact conj_post_slideL (k := k) _ _ _ _ _ _ _ (P.W.dot_mem i _) _ _ hS _ _ _ hf

theorem postCrossNe_slideR (i j : I) (hij : i ≠ j) (t : Sector I)
    (hv₁ : StepValid (true, i) false t)
    (hv₂ : StepValid (true, j) false (nextSector (true, i) false t))
    (hw₁ : StepValid (true, j) false t)
    (hw₂ : StepValid (true, i) false (nextSector (true, j) false t))
    (hs : nextSector (true, j) false (nextSector (true, i) false t) =
      nextSector (true, i) false (nextSector (true, j) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, j) false t))) :
    P.postCrossNe i j t hv₁ hv₂ hw₁ hw₂ hs Z ≫
        homContentPostDot P.T.obj P.W j t.1 (P.muP t) (P.muM_postE j hw₁)
          ((P.step (true, i) false _ hw₂).obj Z) =
      zsign k (D.parity i * D.parity j) • ((P.step (true, i) false t hv₁).map
          (homContentPostDot P.T.obj P.W j (nextSector (true, i) false t).1 (P.muP _)
            (P.muM_postE j hv₂) (hs ▸ Z : P.H (nextSector (true, j) false (nextSector (true, i) false t)))) ≫
        P.postCrossNe i j t hv₁ hv₂ hw₁ hw₂ hs Z) := by
  have h₃ : P.muM (nextSector (true, j) false (nextSector (true, i) false t)) + D.α i =
      P.muM (nextSector (true, j) false t) := by
    rw [hs]; exact P.muM_postE i hw₂
  have hS := P.reservoirRel.slideRight i j hij (P.muM_postE j hv₂) (P.muM_postE i hv₁) h₃
    (P.muM_postE j hw₁)
  have hf : homContentPostDot P.T.obj P.W j t.1 (P.muP t) (P.muM_postE j hw₁)
        ((homContentPostE P.T.obj P.W i t.1 (P.muP _) h₃).obj (hs ▸ Z : P.H (nextSector (true, j) false (nextSector (true, i) false t)))) ≫
        (P.step (true, j) false t hw₁).map
          (eqToHom (eq_of_heq (P.postE_obj_heq i t.1 hs h₃ (P.muM_postE i hw₂) Z))) =
      (P.step (true, j) false t hw₁).map
          (eqToHom (eq_of_heq (P.postE_obj_heq i t.1 hs h₃ (P.muM_postE i hw₂) Z))) ≫
        homContentPostDot P.T.obj P.W j t.1 (P.muP t) (P.muM_postE j hw₁)
          ((P.step (true, i) false _ hw₂).obj Z) := by
    have hx := TwoSupercategory.super_interchange (R := k)
      (eqToHom_mem_zero (k := k) (eq_of_heq (P.postE_obj_heq i t.1 hs h₃ (P.muM_postE i hw₂) Z)))
      (P.W.dot_mem j (P.muM_postE j hw₁))
    rw [koszulSign_zero_left, one_smul] at hx
    have hm := congrArg (homParityShift (k := k) (homContentShift D j t.1)).map hx.symm
    rw [Functor.map_comp, Functor.map_comp] at hm
    exact hm
  exact conj_post_slideR (k := k) _ _ _ _ _ _ _ (P.W.dot_mem j _) _ _ hS _ _ _ hf

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
