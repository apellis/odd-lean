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

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
