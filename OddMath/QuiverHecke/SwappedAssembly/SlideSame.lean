/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.QuadSame
import OddMath.QuiverHecke.SwappedAssembly.SlideBlocks
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExistence

/-! # The same-colour slide relations for the swapped crossing

The relations `slideLEq` and `slideREq` of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, (1.8), on `Eᵢ Eᵢ`, for the image `crossImage` of the upward crossing in
the swapped action (`docs/Nondegeneracy/SwappedActionAssembly.md`, §3, rows `slideLEq`,
`slideREq`).

The dots are diagonal (`leftDot_swapped_probe`, ...). On the path `PP` the slides are the
factor slides of the probe family, on `RR` those of the reservoir family. On the mixed pair the
dots intertwine across the mixed interchange `J` with the colour sign
(`prPreDot_comp_mixedJ`, `prPostDot_comp_mixedJ`), and `SlideBlocks` reduces the four entries to
the two diagonal identities of the coefficient `a`, which hold for the coefficient
`crossCoeffOfInputs` (§2, (A6)).
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace SlideBlocks

open CategoryTheory Preadditive

variable {C : Type*} [Category C] [Preadditive C] {U : C}

/-- **Odd diagonal entry from its characterizing identity.** If `x`, `y` anticommute,
`x ≫ x - y ≫ y` is a unit `u` and `(x ≫ x - y ≫ y) ≫ a = x - y`, then `a` satisfies both
diagonal slide identities with `q = -1` for the left dot `y` and the right dot `x`. -/
theorem slide_of_odd_identity {x y a : End U} (u : (End U)ˣ) (hu : (u : End U) = x * x - y * y)
    (hxy : x ≫ y = -(y ≫ x)) (ha : (x ≫ x - y ≫ y) ≫ a = x - y) :
    (y ≫ a - (-1 : ℤ) • (a ≫ x) = 𝟙 _) ∧ (a ≫ y - (-1 : ℤ) • (x ≫ a) = 𝟙 _) ∧
    (y ≫ a ≫ a = a ≫ a ≫ y) ∧ (x ≫ a ≫ a = a ≫ a ≫ x) := by
  have hxy' : y * x = -(x * y) := hxy
  have hc1 : Commute x (y * y) := by
    show x * (y * y) = y * y * x
    have h' : x * y = -(y * x) := by rw [hxy', neg_neg]
    rw [← mul_assoc, h', neg_mul, mul_assoc, h', mul_neg, neg_neg, ← mul_assoc]
  have hc2 : Commute y (x * x) := by
    show y * (x * x) = x * x * y
    rw [← mul_assoc, hxy', neg_mul, mul_assoc, hxy', mul_neg, neg_neg, ← mul_assoc]
  have hux : Commute (u : End U) x := by
    rw [hu]; exact (((Commute.refl x).mul_right (Commute.refl x)).sub_right hc1).symm
  have huy : Commute (u : End U) y := by
    rw [hu]; exact (hc2.sub_right ((Commute.refl y).mul_right (Commute.refl y))).symm
  have hix : Commute (↑u⁻¹ : End U) x := hux.units_inv_left
  have hiy : Commute (↑u⁻¹ : End U) y := huy.units_inv_left
  have ha' : a * u = x - y := by rw [hu]; exact ha
  have hau : a = ↑u⁻¹ * (x - y) := by
    rw [(hix.sub_right hiy).eq, ← ha', mul_assoc, Units.mul_inv, mul_one]
  refine SlideBlocks.slide_of_inv_odd (w := -(↑u⁻¹ : End U)) ?_ ?_ ?_ ?_ ?_
  · show x * y = -(y * x); rw [hxy', neg_neg]
  · show -(↑u⁻¹ : End U) * (y * y - x * x) = 1
    rw [neg_mul, ← mul_neg, neg_sub, ← hu, Units.inv_mul]
  · show y * -(↑u⁻¹ : End U) = -(↑u⁻¹ : End U) * y
    rw [mul_neg, neg_mul, hiy.eq]
  · show x * -(↑u⁻¹ : End U) = -(↑u⁻¹ : End U) * x
    rw [mul_neg, neg_mul, hix.eq]
  · show a = -(↑u⁻¹ : End U) * (y - x)
    rw [hau, neg_mul, ← mul_neg, neg_sub]

/-- A slide identity with the dots before and after the crossing exchanged, transported along
an isomorphism that intertwines the dots. -/
theorem conj_slide_left {A B' : C} (φ : A ≅ B') (c g₁ g₂ : B' ⟶ B') (d₁ d₂ : A ⟶ A) (q : ℤ)
    (h₂ : d₂ ≫ φ.hom = φ.hom ≫ g₂) (h₁ : d₁ ≫ φ.hom = φ.hom ≫ g₁)
    (hs : g₁ ≫ c - q • (c ≫ g₂) = 𝟙 _) :
    d₁ ≫ (φ.hom ≫ c ≫ φ.inv) - q • ((φ.hom ≫ c ≫ φ.inv) ≫ d₂) = 𝟙 _ := by
  have h₂' : φ.inv ≫ d₂ = g₂ ≫ φ.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h₂, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  calc d₁ ≫ (φ.hom ≫ c ≫ φ.inv) - q • ((φ.hom ≫ c ≫ φ.inv) ≫ d₂)
      = φ.hom ≫ (g₁ ≫ c - q • (c ≫ g₂)) ≫ φ.inv := by
        rw [reassoc_of% h₁, Category.assoc, Category.assoc, h₂']
        simp only [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.zsmul_comp,
          Preadditive.comp_zsmul, Category.assoc]
    _ = 𝟙 _ := by rw [hs, Category.id_comp, Iso.hom_inv_id]

end SlideBlocks

/-! ## Conjugating a factor slide by the associator -/

section Conj

variable {a b c d : B} {E₁ : a ⟶ b} {E₂ : b ⟶ c} (Z : c ⟶ d)
include k
omit [∀ a b : B, PiSupercategory k (a ⟶ b)]

theorem conj_comp (f g : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    (associator E₁ E₂ Z).inv ≫ (f ≫ g) ▷ Z ≫ (associator E₁ E₂ Z).hom =
      ((associator E₁ E₂ Z).inv ≫ f ▷ Z ≫ (associator E₁ E₂ Z).hom) ≫
        ((associator E₁ E₂ Z).inv ≫ g ▷ Z ≫ (associator E₁ E₂ Z).hom) := by
  rw [TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem conj_whiskerLeft (x₂ : E₂ ⟶ E₂) :
    (associator E₁ E₂ Z).inv ≫ (E₁ ◁ x₂) ▷ Z ≫ (associator E₁ E₂ Z).hom = E₁ ◁ (x₂ ▷ Z) := by
  rw [TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem conj_whiskerRight (x₁ : E₁ ⟶ E₁) :
    (associator E₁ E₂ Z).inv ≫ (x₁ ▷ E₂) ▷ Z ≫ (associator E₁ E₂ Z).hom = x₁ ▷ (E₂ ≫ Z) := by
  rw [TwoSupercategory.whiskerRight_comp (R := k)]

theorem conj_slide_identity (u v : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (q : ℤ) (h : u - q • v = 𝟙 _) :
    (associator E₁ E₂ Z).inv ≫ u ▷ Z ≫ (associator E₁ E₂ Z).hom -
      q • ((associator E₁ E₂ Z).inv ≫ v ▷ Z ≫ (associator E₁ E₂ Z).hom) = 𝟙 _ := by
  have hs := congrArg (fun f => (associator E₁ E₂ Z).inv ≫ f ▷ Z ≫
    (associator E₁ E₂ Z).hom) h
  simp only [sub_eq_add_neg, TwoSupercategory.add_whiskerRight (R := k),
    TwoSupercategory.neg_whiskerRight (R := k), TwoSupercategory.zsmul_whiskerRight (R := k),
    TwoSupercategory.id_whiskerRight (R := k), Preadditive.comp_add, Preadditive.add_comp,
    Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.id_comp, Iso.inv_hom_id] at hs
  simpa only [sub_eq_add_neg] using hs

/-- **Both slides of the conjugated crossing** `C = -q (α⁻¹ ≫ t ▷ Z ≫ α)` from the two factor
slides of `t`, with `q² = 1`. -/
theorem conj_crossing_slides (x₁ : E₁ ⟶ E₁) (x₂ : E₂ ⟶ E₂) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (q : ℤ)
    (hq : q * q = 1) (hl : E₁ ◁ x₂ ≫ t - q • (t ≫ x₁ ▷ E₂) = 𝟙 _)
    (hr : t ≫ E₁ ◁ x₂ - q • (x₁ ▷ E₂ ≫ t) = 𝟙 _) :
    (x₁ ▷ (E₂ ≫ Z) ≫ ((-q) • ((associator E₁ E₂ Z).inv ≫ t ▷ Z ≫ (associator E₁ E₂ Z).hom)) -
        q • (((-q) • ((associator E₁ E₂ Z).inv ≫ t ▷ Z ≫ (associator E₁ E₂ Z).hom)) ≫
          E₁ ◁ (x₂ ▷ Z)) = 𝟙 _) ∧
    (((-q) • ((associator E₁ E₂ Z).inv ≫ t ▷ Z ≫ (associator E₁ E₂ Z).hom)) ≫
          x₁ ▷ (E₂ ≫ Z) -
        q • (E₁ ◁ (x₂ ▷ Z) ≫
          ((-q) • ((associator E₁ E₂ Z).inv ≫ t ▷ Z ≫ (associator E₁ E₂ Z).hom))) = 𝟙 _) := by
  replace hl := conj_slide_identity (k := k) Z _ _ q hl
  replace hr := conj_slide_identity (k := k) Z _ _ q hr
  rw [conj_comp (k := k), conj_comp (k := k), conj_whiskerLeft (k := k),
    conj_whiskerRight (k := k)] at hl hr
  set A := (associator E₁ E₂ Z).inv ≫ t ▷ Z ≫ (associator E₁ E₂ Z).hom
  constructor
  · rw [← hr]
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, smul_smul, neg_smul,
      Preadditive.comp_neg, Preadditive.neg_comp, smul_neg, hq, one_smul]
    abel
  · rw [← hl]
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, smul_smul, neg_smul,
      Preadditive.comp_neg, Preadditive.neg_comp, smul_neg, hq, one_smul]
    abel

end Conj

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-! ## The dots at explicit paths -/

theorem leftDot_swapped_probe (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I) (ν : X)
    (s : Sector I) (σ₂ : Bool) (hv₂ : StepValid (true, j) σ₂ (nextSector (true, i) true s))
    (Z : P.H (nextSector (true, j) σ₂ (nextSector (true, i) true s))) :
    leftDot (P.swappedGens c L) i j ν (.cons _ true s trivial (.cons _ σ₂ _ hv₂ (.nil _))) Z =
      P.T.dot i _ ▷ (P.step (true, j) σ₂ _ hv₂).obj Z := by
  rw [leftDot_cons]
  exact P.dotImage_probe i (SKM.wt D ν [up j]) s trivial trivial
    ((P.step (true, j) σ₂ _ hv₂).obj Z)

theorem leftDot_swapped_reservoir (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I)
    (ν : X) (s : Sector I) (hv₁ : StepValid (true, i) false s) (σ₂ : Bool)
    (hv₂ : StepValid (true, j) σ₂ (nextSector (true, i) false s))
    (Z : P.H (nextSector (true, j) σ₂ (nextSector (true, i) false s))) :
    leftDot (P.swappedGens c L) i j ν (.cons _ false s hv₁ (.cons _ σ₂ _ hv₂ (.nil _))) Z =
      homContentPostDot P.T.obj P.W i s.1 (P.muP s) _ ((P.step (true, j) σ₂ _ hv₂).obj Z) := by
  rw [leftDot_cons]
  exact P.dotImage_reservoir i (SKM.wt D ν [up j]) s hv₁ hv₁
    ((P.step (true, j) σ₂ _ hv₂).obj Z)

theorem rightDot_swapped_probe (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I) (ν : X)
    (s : Sector I) (σ₁ : Bool) (hv₁ : StepValid (true, i) σ₁ s)
    (Z : P.H (nextSector (true, j) true (nextSector (true, i) σ₁ s))) :
    rightDot (P.swappedGens c L) i j ν (.cons _ σ₁ s hv₁ (.cons _ true _ trivial (.nil _))) Z =
      (P.step (true, i) σ₁ s hv₁).map (P.T.dot j _ ▷ Z) := by
  rw [rightDot_cons]
  exact congrArg _ (P.dotImage_probe j ν _ trivial trivial Z)

theorem rightDot_swapped_reservoir (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I)
    (ν : X) (s : Sector I) (σ₁ : Bool) (hv₁ : StepValid (true, i) σ₁ s)
    (hv₂ : StepValid (true, j) false (nextSector (true, i) σ₁ s))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) σ₁ s))) :
    rightDot (P.swappedGens c L) i j ν (.cons _ σ₁ s hv₁ (.cons _ false _ hv₂ (.nil _))) Z =
      (P.step (true, i) σ₁ s hv₁).map (homContentPostDot P.T.obj P.W j
        (nextSector (true, i) σ₁ s).1 (P.muP _) _ Z) := by
  rw [rightDot_cons]
  exact congrArg _ (P.dotImage_reservoir j ν _ hv₂ hv₂ Z)

/-! ## The dots across the mixed interchange -/

private theorem shift_sum (i : I) (β : I →₀ ℕ) :
    koszulSign (homContentShift D i (β + Finsupp.single i 1) + homContentShift D i β)
      (D.parity i) = koszulSign (D.parity i) (D.parity i) := by
  rw [homContentShift_add_single]
  congr 1
  generalize homContentShift D i β = a
  generalize D.parity i = p
  fin_cases a <;> fin_cases p <;> decide

/-- The probe dot moves across the same-colour mixed interchange with the colour sign. -/
theorem prPreDot_comp_mixedJ (i : I) (t : Sector I)
    (hv : StepValid (true, i) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) true t))) :
    P.prPreDot i i t hv Z ≫ (P.mixedJ i i t hv Z).hom =
      koszulSign (D.parity i) (D.parity i) • ((P.mixedJ i i t hv Z).hom ≫
        P.rpPreDot i t hv Z) := by
  have h := homMixedInterchange_pre (k := k) (P.T.E i (P.muP_preE i t))
    (P.W.E i (P.muM_postE i hv)) (homContentShift D i (t.1 + Finsupp.single i 1))
    (homContentShift D i t.1) Z (P.T.dot i _) (P.T.dot_mem i _)
  rw [shift_sum] at h
  exact h

/-- The reservoir dot moves across the same-colour mixed interchange with the colour sign. -/
theorem prPostDot_comp_mixedJ (i : I) (t : Sector I)
    (hv : StepValid (true, i) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) true t))) :
    P.prPostDot i i t hv Z ≫ (P.mixedJ i i t hv Z).hom =
      koszulSign (D.parity i) (D.parity i) • ((P.mixedJ i i t hv Z).hom ≫
        P.rpPostDot i t hv Z) := by
  have h := homMixedInterchange_post (k := k) (P.T.E i (P.muP_preE i t))
    (P.W.E i (P.muM_postE i hv)) (homContentShift D i (t.1 + Finsupp.single i 1))
    (homContentShift D i t.1) Z (P.W.dot i _) (P.W.dot_mem i _)
  rw [shift_sum] at h
  exact h

/-! ## The slides on the paths `PP` and `RR` -/

/-- The probe dot on the outer letter of the path `(P,P)` of `Eᵢ Eᵢ`. -/
def ppLeftDot (i : I) (t : Sector I)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) true t))) :
    End ((P.step (true, i) true t trivial).obj ((P.step (true, i) true _ trivial).obj Z)) :=
  P.T.dot i (P.muP_preE i t) ▷ (P.step (true, i) true _ trivial).obj Z

/-- The probe dot on the inner letter of the path `(P,P)` of `Eᵢ Eᵢ`. -/
def ppRightDot (i : I) (t : Sector I)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) true t))) :
    End ((P.step (true, i) true t trivial).obj ((P.step (true, i) true _ trivial).obj Z)) :=
  (P.step (true, i) true t trivial).map (P.T.dot i (P.muP_preE i _) ▷ Z)

/-- The reservoir dot on the outer letter of the path `(R,R)` of `Eᵢ Eᵢ`. -/
def rrLeftDot (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) false t))) :
    End ((P.step (true, i) false t hv).obj ((P.step (true, i) false _ hw).obj Z)) :=
  homContentPostDot P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)
    ((P.step (true, i) false _ hw).obj Z)

/-- The reservoir dot on the inner letter of the path `(R,R)` of `Eᵢ Eᵢ`. -/
def rrRightDot (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) false t))) :
    End ((P.step (true, i) false t hv).obj ((P.step (true, i) false _ hw).obj Z)) :=
  (P.step (true, i) false t hv).map (homContentPostDot P.T.obj P.W i
    (nextSector (true, i) false t).1 (P.muP _) (P.muM_postE i hw) Z)

/-- **The slides of the probe/probe entry.** -/
theorem preCrossSame_slides (i : I) (t : Sector I)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) true t))) :
    (P.ppLeftDot i t Z ≫ P.preCrossSame i t Z - koszulSign (D.parity i) (D.parity i) •
        (P.preCrossSame i t Z ≫ P.ppRightDot i t Z) = 𝟙 _) ∧
    (P.preCrossSame i t Z ≫ P.ppLeftDot i t Z - koszulSign (D.parity i) (D.parity i) •
        (P.ppRightDot i t Z ≫ P.preCrossSame i t Z) = 𝟙 _) :=
  conj_crossing_slides (k := k) Z (P.T.dot i (P.muP_preE i t)) (P.T.dot i (P.muP_preE i _))
    _ _ (koszulSign_mul_self _ _) (P.T.loc i (P.muP_preE i t) (P.muP_preE i _)).slide_left
    (P.T.loc i (P.muP_preE i t) (P.muP_preE i _)).slide_right

/-- **The slides of the reservoir/reservoir entry.** -/
theorem postCrossSame_slides (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) false t))) :
    (P.rrLeftDot i t hv hw Z ≫ P.postCrossSame i t hv hw Z -
        koszulSign (D.parity i) (D.parity i) •
          (P.postCrossSame i t hv hw Z ≫ P.rrRightDot i t hv hw Z) = 𝟙 _) ∧
    (P.postCrossSame i t hv hw Z ≫ P.rrLeftDot i t hv hw Z -
        koszulSign (D.parity i) (D.parity i) •
          (P.rrRightDot i t hv hw Z ≫ P.postCrossSame i t hv hw Z) = 𝟙 _) := by
  refine ⟨?_, homContentPostCrossing_slide_app P.T.obj P.W i t.1 (P.muP t) _ _ Z⟩
  have hs := congrArg (fun g => Z ◁ g)
    (P.W.loc i (P.muM_postE i hw) (P.muM_postE i hv)).slide_left
  rw [sub_eq_add_neg, TwoSupercategory.whiskerLeft_add (R := k),
    TwoSupercategory.whiskerLeft_neg (R := k), TwoSupercategory.whiskerLeft_zsmul (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whiskerLeft_id (R := k), ← sub_eq_add_neg] at hs
  exact SlideBlocks.conj_slide_left
    ((homContentPostWordIso P.T.obj P.W i t.1 (P.muP t) _ _).app Z) _ _ _ _ _ _
    (homContentPostDot_inner_wordIso P.T.obj P.W i t.1 (P.muP t) _ _ Z)
    (homContentPostDot_outer_wordIso P.T.obj P.W i t.1 (P.muP t) _ _ Z) hs

/-- **The diagonal identities of the coefficient** on the path `(R,P)`: with the left dot
`y = rpPostDot` and the right dot `x = rpPreDot`, `y a - q a x = 1`, `a y - q x a = 1`, and
`a ≫ a` commutes with both dots. The odd case uses the invertibility of `x² - y²`
(`CrossCoeffInputs`). -/
theorem crossCoeff_diag (c : P.CrossCoeff Sc) (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t))) :
    (P.rpPostDot i t hv Z ≫ c.a i t hv Z - koszulSign (D.parity i) (D.parity i) •
        (c.a i t hv Z ≫ P.rpPreDot i t hv Z) = 𝟙 _) ∧
      (c.a i t hv Z ≫ P.rpPostDot i t hv Z - koszulSign (D.parity i) (D.parity i) •
        (P.rpPreDot i t hv Z ≫ c.a i t hv Z) = 𝟙 _) ∧
      (P.rpPostDot i t hv Z ≫ c.a i t hv Z ≫ c.a i t hv Z =
        c.a i t hv Z ≫ c.a i t hv Z ≫ P.rpPostDot i t hv Z) ∧
      (P.rpPreDot i t hv Z ≫ c.a i t hv Z ≫ c.a i t hv Z =
        c.a i t hv Z ≫ c.a i t hv Z ≫ P.rpPreDot i t hv Z) := by
  have hxy := P.rpPreDot_comp_rpPostDot i t hv Z
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hp | hp
  · rw [hp] at hxy ⊢
    have h1 : koszulSign (0 : ZMod 2) 0 = 1 := by decide
    rw [h1, one_smul] at hxy
    rw [h1]
    exact SlideBlocks.slide_of_inv_even hxy.symm (hc.even i hp t hv Z).1 (hc.even i hp t hv Z).2
  · rw [hp] at hxy ⊢
    have h1 : koszulSign (1 : ZMod 2) 1 = -1 := by decide
    rw [h1, neg_one_smul] at hxy
    rw [h1]
    have hd : ((P.crossDenom h i t hv Z : (End (P.rpObj i i t hv Z))ˣ) :
        End (P.rpObj i i t hv Z)) = P.rpPreDot i t hv Z * P.rpPreDot i t hv Z -
          P.rpPostDot i t hv Z * P.rpPostDot i t hv Z := by
      have hi0 : D.parity i ≠ 0 := by rw [hp]; decide
      simp [crossDenom, hi0, sub_eq_add_neg, add_comm, pow_two]
    exact SlideBlocks.slide_of_odd_identity _ hd hxy (hc.odd i hp t hv Z).2


private theorem zsign_mul_self_smul {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A A' : C} (p : ZMod 2) (f : A ⟶ A') :
    zsign k (p * p) • f = koszulSign p p • f := by
  rcases Supercategory.parity_eq_zero_or_one p with rfl | rfl <;> simp [zsign, koszulSign]

/-! ## The assembled same-colour slides -/

open Classical in
/-- **The same-colour slides `slideLEq` and `slideREq`** for the swapped generators, entry by
entry, for a crossing coefficient satisfying its characterizing identities under the inputs
F2, F3 of the written proof (`CrossCoeffInputs`). -/
theorem swappedGens_slideEq (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hin : P.CrossCoeffInputs)
    (L : P.LeftwardData) (i : I) (ν : X) {s t : Sector I}
    (p q : SPath (wd D ν [up i, up i]) s t) (Z : P.H t) :
    (leftDot (P.swappedGens c L) i i ν p Z ≫ (P.swappedGens c L).cross i i ν p q Z -
        zsign k (D.parity i * D.parity i) •
          ((P.swappedGens c L).cross i i ν p q Z ≫ rightDot (P.swappedGens c L) i i ν q Z) =
      if hpq : p = q then eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0) ∧
    ((P.swappedGens c L).cross i i ν p q Z ≫ leftDot (P.swappedGens c L) i i ν q Z -
        zsign k (D.parity i * D.parity i) •
          (rightDot (P.swappedGens c L) i i ν p Z ≫ (P.swappedGens c L).cross i i ν p q Z) =
      if hpq : p = q then eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0) := by
  obtain ⟨σ₁, σ₂, hv₁, hv₂, e₁, hp⟩ := SPath.exists_eq_mk₂ p
  subst e₁
  obtain ⟨τ₁, τ₂, hw₁, hw₂, e₂, hq⟩ := SPath.exists_eq_mk₂ q
  have he := congrArg (fun x : Sector I => x.1 i) e₂
  simp only [nextSector_fst_same] at he
  rw [zsign_mul_self_smul, zsign_mul_self_smul]
  have hqq := koszulSign_mul_self (D.parity i) (D.parity i)
  cases σ₁ <;> cases σ₂ <;> cases τ₁ <;> cases τ₂ <;> try (simp at he <;> omega)
  case true.true.true.true =>
    obtain rfl : p = .cons _ true s trivial (.cons _ true _ trivial (.nil _)) := hp
    obtain rfl : q = .cons _ true s trivial (.cons _ true _ trivial (.nil _)) := hq
    rw [dite_eq_left rfl, eqToHom_refl, leftDot_swapped_probe, rightDot_swapped_probe,
      swappedGens_cross_self]
    exact P.preCrossSame_slides i s Z
  case false.false.false.false =>
    obtain rfl : p = .cons _ false s hv₁ (.cons _ false _ hv₂ (.nil _)) := hp
    obtain rfl : q = .cons _ false s hv₁ (.cons _ false _ hv₂ (.nil _)) := hq
    rw [dite_eq_left rfl, eqToHom_refl, leftDot_swapped_reservoir, rightDot_swapped_reservoir,
      swappedGens_cross_self]
    exact P.postCrossSame_slides i s hv₁ hv₂ Z
  case false.true.false.true =>
    obtain rfl : p = .cons _ false s hv₁ (.cons _ true _ trivial (.nil _)) := hp
    obtain rfl : q = .cons _ false s hv₁ (.cons _ true _ trivial (.nil _)) := hq
    obtain ⟨hb₁, hb₂, hcl, hcr⟩ := P.crossCoeff_diag c hc hin i s hv₁ Z
    have hl := SlideBlocks.mixedBlock_slideL hqq
      (P.mixedJ i i s hv₁ Z).hom_inv_id (P.mixedJ i i s hv₁ Z).inv_hom_id
      (P.prPreDot_comp_mixedJ i s hv₁ Z) (P.prPostDot_comp_mixedJ i s hv₁ Z) hb₁ hb₂ hcl
    have hr := SlideBlocks.mixedBlock_slideR hqq
      (P.mixedJ i i s hv₁ Z).hom_inv_id (P.mixedJ i i s hv₁ Z).inv_hom_id
      (P.prPreDot_comp_mixedJ i s hv₁ Z) (P.prPostDot_comp_mixedJ i s hv₁ Z) hb₁ hb₂ hcr
    rw [dite_eq_left rfl, eqToHom_refl]
    rw [leftDot_swapped_reservoir, rightDot_swapped_probe, swappedGens_cross_self]
    exact ⟨hl.1, hr.1⟩
  case false.true.true.false =>
    obtain rfl : p = .cons _ false s hv₁ (.cons _ true _ trivial (.nil _)) := hp
    obtain rfl : q = .cons _ true s trivial (.cons _ false _ hv₁ (.nil _)) := hq
    obtain ⟨hb₁, hb₂, hcl, hcr⟩ := P.crossCoeff_diag c hc hin i s hv₁ Z
    have hl := SlideBlocks.mixedBlock_slideL hqq
      (P.mixedJ i i s hv₁ Z).hom_inv_id (P.mixedJ i i s hv₁ Z).inv_hom_id
      (P.prPreDot_comp_mixedJ i s hv₁ Z) (P.prPostDot_comp_mixedJ i s hv₁ Z) hb₁ hb₂ hcl
    have hr := SlideBlocks.mixedBlock_slideR hqq
      (P.mixedJ i i s hv₁ Z).hom_inv_id (P.mixedJ i i s hv₁ Z).inv_hom_id
      (P.prPreDot_comp_mixedJ i s hv₁ Z) (P.prPostDot_comp_mixedJ i s hv₁ Z) hb₁ hb₂ hcr
    rw [dite_eq_right (fun h => by cases h)]
    rw [leftDot_swapped_reservoir, leftDot_swapped_probe, rightDot_swapped_probe,
      rightDot_swapped_reservoir, swappedGens_cross_self]
    exact ⟨hl.2.1, hr.2.1⟩
  case true.false.false.true =>
    obtain rfl : p = .cons _ true s trivial (.cons _ false _ hv₂ (.nil _)) := hp
    obtain rfl : q = .cons _ false s hv₂ (.cons _ true _ trivial (.nil _)) := hq
    obtain ⟨hb₁, hb₂, hcl, hcr⟩ := P.crossCoeff_diag c hc hin i s hv₂ Z
    have hl := SlideBlocks.mixedBlock_slideL hqq
      (P.mixedJ i i s hv₂ Z).hom_inv_id (P.mixedJ i i s hv₂ Z).inv_hom_id
      (P.prPreDot_comp_mixedJ i s hv₂ Z) (P.prPostDot_comp_mixedJ i s hv₂ Z) hb₁ hb₂ hcl
    have hr := SlideBlocks.mixedBlock_slideR hqq
      (P.mixedJ i i s hv₂ Z).hom_inv_id (P.mixedJ i i s hv₂ Z).inv_hom_id
      (P.prPreDot_comp_mixedJ i s hv₂ Z) (P.prPostDot_comp_mixedJ i s hv₂ Z) hb₁ hb₂ hcr
    rw [dite_eq_right (fun h => by cases h)]
    rw [leftDot_swapped_reservoir, leftDot_swapped_probe, rightDot_swapped_probe,
      rightDot_swapped_reservoir, swappedGens_cross_self]
    exact ⟨hl.2.2.1, hr.2.2.1⟩
  case true.false.true.false =>
    obtain rfl : p = .cons _ true s trivial (.cons _ false _ hv₂ (.nil _)) := hp
    obtain rfl : q = .cons _ true s trivial (.cons _ false _ hv₂ (.nil _)) := hq
    obtain ⟨hb₁, hb₂, hcl, hcr⟩ := P.crossCoeff_diag c hc hin i s hv₂ Z
    have hl := SlideBlocks.mixedBlock_slideL hqq
      (P.mixedJ i i s hv₂ Z).hom_inv_id (P.mixedJ i i s hv₂ Z).inv_hom_id
      (P.prPreDot_comp_mixedJ i s hv₂ Z) (P.prPostDot_comp_mixedJ i s hv₂ Z) hb₁ hb₂ hcl
    have hr := SlideBlocks.mixedBlock_slideR hqq
      (P.mixedJ i i s hv₂ Z).hom_inv_id (P.mixedJ i i s hv₂ Z).inv_hom_id
      (P.prPreDot_comp_mixedJ i s hv₂ Z) (P.prPostDot_comp_mixedJ i s hv₂ Z) hb₁ hb₂ hcr
    rw [dite_eq_left rfl, eqToHom_refl]
    rw [leftDot_swapped_probe, rightDot_swapped_reservoir, swappedGens_cross_self]
    exact ⟨hl.2.2.2, hr.2.2.2⟩

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
