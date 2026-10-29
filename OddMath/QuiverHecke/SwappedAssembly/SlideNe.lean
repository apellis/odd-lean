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

/-! ## The mixed entries -/

section QTransport

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

variable (Sc) in
/-- The parameter polynomial `Q_ij(a, b)` in two endomorphisms, in the shape of `mixedQ`. -/
def qExpr {A : C} (a b : End A) (i j : I) : End A :=
  if D.d i j = 0 then (Sc.t i j : k) • (1 : End A) else
    (Sc.t i j : k) • a ^ D.dn i j + (Sc.t j i : k) • b ^ D.dn j i +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • (a ^ p * b ^ q)

private theorem comp_pow_signed {A A' : C} (g : A ⟶ A') (a' : End A) (a : End A') (e : k)
    (h : g ≫ a = e • (a' ≫ g)) : ∀ n : ℕ, g ≫ a ^ n = e ^ n • ((a' ^ n : End A) ≫ g)
  | 0 => by simp [End.one_def]
  | n + 1 => by
    rw [pow_succ, End.mul_def, ← Category.assoc, h, Linear.smul_comp, Category.assoc,
      comp_pow_signed g a' a e h n, Linear.comp_smul, smul_smul, ← Category.assoc,
      pow_succ, pow_succ, End.mul_def, mul_comm]

private theorem comp_monomial_signed {A A' : C} (g : A ⟶ A') (a' b' : End A) (a b : End A')
    (ea eb : k) (ha : g ≫ a = ea • (a' ≫ g)) (hb : g ≫ b = eb • (b' ≫ g)) (p q : ℕ) :
    g ≫ (a ^ p * b ^ q) = (ea ^ p * eb ^ q) • ((a' ^ p * b' ^ q : End A) ≫ g) := by
  rw [End.mul_def, ← Category.assoc, comp_pow_signed g b' b eb hb, Linear.smul_comp,
    Category.assoc, comp_pow_signed g a' a ea ha, Linear.comp_smul, smul_smul,
    End.mul_def, Category.assoc, mul_comm]

private theorem zmod_two_eq_zero_of_ne_one' {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  fin_cases a
  · rfl
  · exact absurd rfl h

private theorem dn_mul_parity' (i x : I) : (D.dn i x : ZMod 2) * D.parity i = 0 := by
  by_cases hi : D.parity i = 1
  · by_cases hix : i = x
    · subst hix
      simp [SKM.Datum.dn, D.d_self]
    · obtain ⟨m, hm⟩ := D.even_d_of_odd hi x
      have hc : (D.dn i x : ℤ) = m + m := by rw [D.dn_cast hix, hm]
      have : D.dn i x = m.toNat + m.toNat := by omega
      rw [this, hi]
      push_cast
      ring_nf
      rw [show (2 : ZMod 2) = 0 from rfl, mul_zero]
  · rw [zmod_two_eq_zero_of_ne_one' hi, mul_zero]

/-- `Q_ij` is transported along `g` when the two dots move with signs that are trivial on
the powers of an odd colour that occur (`Sc.s_eq_zero`, `Datum.even_d_of_odd`). -/
theorem comp_qExpr {A A' : C} (g : A ⟶ A') (a' b' : End A) (a b : End A') (i j : I)
    (ea eb : k) (ha : g ≫ a = ea • (a' ≫ g)) (hb : g ≫ b = eb • (b' ≫ g))
    (hea : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 → ea ^ n = 1)
    (heb : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 → eb ^ n = 1) :
    g ≫ qExpr Sc a b i j = qExpr Sc a' b' i j ≫ g := by
  unfold qExpr
  split_ifs with hd
  · rw [End.one_def, End.one_def, Linear.comp_smul, Linear.smul_comp, Category.comp_id,
      Category.id_comp]
  · rw [Preadditive.comp_add, Preadditive.comp_add, Preadditive.add_comp,
      Preadditive.add_comp, Linear.comp_smul, Linear.comp_smul, Linear.smul_comp,
      Linear.smul_comp, comp_pow_signed g a' a ea ha, comp_pow_signed g b' b eb hb,
      hea _ (dn_mul_parity' i j), heb _ (dn_mul_parity' j i), one_smul, one_smul]
    congr 1
    erw [Preadditive.comp_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun p _ => ?_
    erw [Preadditive.comp_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun q _ => ?_
    erw [Linear.comp_smul, Linear.smul_comp]
    by_cases hs : Sc.s i j p q = 0
    · rw [hs, zero_smul, zero_smul]
    · rw [comp_monomial_signed g a' b' a b ea eb ha hb p q,
        hea p (zmod_two_eq_zero_of_ne_one' fun h => hs (Sc.s_eq_zero i j p q h)),
        heb q (zmod_two_eq_zero_of_ne_one' fun h => hs (by
          rw [Sc.s_symm]; exact Sc.s_eq_zero j i q p h)), one_mul, one_smul]

/-- A relation `a ≫ J = e (J ≫ a')` with `e² = 1` across an isomorphism, inverted. -/
theorem inv_comp_signed {A A' : C} (J : A ≅ A') (a : End A) (a' : End A') (e : k)
    (he : e * e = 1) (h : a ≫ J.hom = e • (J.hom ≫ a')) :
    a' ≫ J.inv = e • (J.inv ≫ a) := by
  have h' : J.inv ≫ a ≫ J.hom = e • a' := by
    rw [h, Linear.comp_smul, Iso.inv_hom_id_assoc]
  calc a' ≫ J.inv = (e * e) • (a' ≫ J.inv) := by rw [he, one_smul]
    _ = e • ((e • a') ≫ J.inv) := by rw [Linear.smul_comp, smul_smul]
    _ = e • (J.inv ≫ a) := by rw [← h', Category.assoc, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]

end QTransport

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] [TwoSupercategory k B] in
theorem koszulSign_smul_eq_zsign {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A A' : C} (p q : ZMod 2) (f : A ⟶ A') :
    koszulSign p q • f = zsign k (p * q) • f := by
  rcases Supercategory.parity_eq_zero_or_one p with rfl | rfl <;>
    rcases Supercategory.parity_eq_zero_or_one q with rfl | rfl <;> simp [zsign, koszulSign]

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] [TwoSupercategory k B] in
theorem zsign_pow_of_mul_eq_zero (p q : ZMod 2) (n : ℕ) (hn : (n : ZMod 2) * p = 0) :
    zsign k (p * q) ^ n = 1 := by
  rcases Supercategory.parity_eq_zero_or_one p with rfl | rfl
  · simp [zsign]
  · rw [mul_one] at hn
    obtain ⟨m, rfl⟩ := (ZMod.natCast_eq_zero_iff n 2).1 hn
    rw [pow_mul, sq, zsign_mul_self', one_pow]

private theorem shift_sum_ne (i j : I) (β : I →₀ ℕ) :
    homContentShift D j (β + Finsupp.single i 1) + homContentShift D j β =
      D.parity i * D.parity j := by
  rw [homContentShift_add_single, mul_comm]
  generalize homContentShift D j β = a
  generalize D.parity i * D.parity j = b
  fin_cases a <;> fin_cases b <;> decide

private theorem mul_left_self (p q : ZMod 2) : p * q * p = p * q := by
  fin_cases p <;> fin_cases q <;> decide

private theorem mul_right_self (p q : ZMod 2) : p * q * q = p * q := by
  fin_cases p <;> fin_cases q <;> decide

/-- The probe dot moves across the distinct-colour mixed interchange. -/
theorem prPreDot_comp_mixedJ_ne (i j : I) (t : Sector I)
    (hv : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    P.prPreDot i j t hv Z ≫ (P.mixedJ i j t hv Z).hom =
      zsign k (D.parity i * D.parity j) • ((P.mixedJ i j t hv Z).hom ≫
        (P.step (true, j) false t hv).map (P.T.dot i (P.muP_preE i t) ▷ Z)) := by
  have h := homMixedInterchange_pre (k := k) (P.T.E i (P.muP_preE i t))
    (P.W.E j (P.muM_postE j hv)) (homContentShift D j (t.1 + Finsupp.single i 1))
    (homContentShift D j t.1) Z (P.T.dot i _) (P.T.dot_mem i _)
  rw [shift_sum_ne, koszulSign_smul_eq_zsign (k := k), mul_left_self] at h
  exact h

/-- The reservoir dot moves across the distinct-colour mixed interchange. -/
theorem prPostDot_comp_mixedJ_ne (i j : I) (t : Sector I)
    (hv : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    P.prPostDot i j t hv Z ≫ (P.mixedJ i j t hv Z).hom =
      zsign k (D.parity i * D.parity j) • ((P.mixedJ i j t hv Z).hom ≫
        homContentPostDot P.T.obj P.W j t.1 (P.muP t) (P.muM_postE j hv)
          ((P.step (true, i) true (nextSector (true, j) false t) trivial).obj Z)) := by
  have h := homMixedInterchange_post (k := k) (P.T.E i (P.muP_preE i t))
    (P.W.E j (P.muM_postE j hv)) (homContentShift D j (t.1 + Finsupp.single i 1))
    (homContentShift D j t.1) Z (P.W.dot j _) (P.W.dot_mem j _)
  rw [shift_sum_ne, koszulSign_smul_eq_zsign (k := k), mul_right_self] at h
  exact h

/-- The two dots on the path `(P,R)` of `Eᵢ Eⱼ` supercommute. -/
theorem prPostDot_comp_prPreDot (i j : I) (t : Sector I)
    (hv : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    P.prPostDot i j t hv Z ≫ P.prPreDot i j t hv Z =
      zsign k (D.parity i * D.parity j) • (P.prPreDot i j t hv Z ≫ P.prPostDot i j t hv Z) := by
  have hy : homContentPostDot P.T.obj P.W j (nextSector (true, i) true t).1
      (P.muP (nextSector (true, i) true t)) (P.muM_postE j hv) Z ∈
        parity (R := k) _ _ (D.parity j) :=
    IsSuperfunctor.map_mem (R := k) (F := homParityShift (k := k) _)
      (TwoSupercategory.whiskerLeft_mem Z (P.W.dot_mem j _))
  have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i (P.muP_preE i t)) hy
  rw [koszulSign_smul_eq_zsign (k := k)] at h
  have h' := congrArg (zsign k (D.parity i * D.parity j) • ·) h
  simp only [smul_smul, zsign_mul_self', one_smul] at h'
  exact h'.symm

/-- **The slides of the probe/reservoir entry** `J` of the distinct-colour crossing. -/
theorem mixedJ_ne_slides (i j : I) (t : Sector I)
    (hv : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    (P.prPreDot i j t hv Z ≫ (P.mixedJ i j t hv Z).hom =
      zsign k (D.parity i * D.parity j) • ((P.mixedJ i j t hv Z).hom ≫
        (P.step (true, j) false t hv).map (P.T.dot i (P.muP_preE i t) ▷ Z))) ∧
    ((P.mixedJ i j t hv Z).hom ≫
        homContentPostDot P.T.obj P.W j t.1 (P.muP t) (P.muM_postE j hv)
          ((P.step (true, i) true (nextSector (true, j) false t) trivial).obj Z) =
      zsign k (D.parity i * D.parity j) • (P.prPostDot i j t hv Z ≫
        (P.mixedJ i j t hv Z).hom)) := by
  refine ⟨P.prPreDot_comp_mixedJ_ne i j t hv Z, ?_⟩
  rw [P.prPostDot_comp_mixedJ_ne i j t hv Z, smul_smul, zsign_mul_self', one_smul]

/-- The parameter polynomial on the path `(P,R)` commutes with both dots. -/
theorem mixedQ_comm (i j : I) (t : Sector I)
    (hv : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    P.prPostDot i j t hv Z ≫ P.mixedQ i j t hv Z = P.mixedQ i j t hv Z ≫ P.prPostDot i j t hv Z ∧
    P.prPreDot i j t hv Z ≫ P.mixedQ i j t hv Z = P.mixedQ i j t hv Z ≫ P.prPreDot i j t hv Z := by
  have hxy := P.prPostDot_comp_prPreDot i j t hv Z
  have hyx : P.prPreDot i j t hv Z ≫ P.prPostDot i j t hv Z =
      zsign k (D.parity i * D.parity j) • (P.prPostDot i j t hv Z ≫ P.prPreDot i j t hv Z) := by
    rw [hxy, smul_smul, zsign_mul_self', one_smul]
  have e1 : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 →
      zsign k (D.parity i * D.parity j) ^ n = 1 :=
    fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn
  have e2 : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 →
      zsign k (D.parity i * D.parity j) ^ n = 1 :=
    fun n hn => by rw [mul_comm]; exact zsign_pow_of_mul_eq_zero _ _ n hn
  refine ⟨comp_qExpr (Sc := Sc) _ _ _ _ _ i j _ 1 hxy (by rw [one_smul]) e1
    (fun _ _ => one_pow _), comp_qExpr (Sc := Sc) _ _ _ _ _ i j 1 _ (by rw [one_smul]) hyx
    (fun _ _ => one_pow _) e2⟩

/-- **The slides of the reservoir/probe entry** `J⁻¹ Q` of the distinct-colour crossing, from
`(R,P)` of `Eᵢ Eⱼ` to `(P,R)` of `Eⱼ Eᵢ`. -/
theorem mixedJinvQ_ne_slides (i j : I) (t : Sector I)
    (hw : StepValid (true, i) false (nextSector (true, j) true t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, j) true t))) :
    (homContentPostDot P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hw)
        ((P.step (true, j) true (nextSector (true, i) false t) trivial).obj Z) ≫
        ((P.mixedJ j i t hw Z).inv ≫ P.mixedQ j i t hw Z) =
      zsign k (D.parity i * D.parity j) • (((P.mixedJ j i t hw Z).inv ≫ P.mixedQ j i t hw Z) ≫
        P.prPostDot j i t hw Z)) ∧
    (((P.mixedJ j i t hw Z).inv ≫ P.mixedQ j i t hw Z) ≫ P.prPreDot j i t hw Z =
      zsign k (D.parity i * D.parity j) • ((P.step (true, i) false t hw).map
        (P.T.dot j (P.muP_preE j t) ▷ Z) ≫ ((P.mixedJ j i t hw Z).inv ≫ P.mixedQ j i t hw Z))) := by
  obtain ⟨hQy, hQx⟩ := P.mixedQ_comm j i t hw Z
  have hpost := inv_comp_signed _ _ _ _ (zsign_mul_self' _) (P.prPostDot_comp_mixedJ_ne j i t hw Z)
  have hpre := inv_comp_signed _ _ _ _ (zsign_mul_self' _) (P.prPreDot_comp_mixedJ_ne j i t hw Z)
  rw [mul_comm (D.parity j)] at hpost hpre
  constructor
  · rw [← Category.assoc, hpost, Linear.smul_comp, Category.assoc, Category.assoc, hQy]
  · rw [Category.assoc, ← hQx, reassoc_of% hpre, Linear.smul_comp, smul_smul, zsign_mul_self',
      one_smul, Category.assoc]

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
