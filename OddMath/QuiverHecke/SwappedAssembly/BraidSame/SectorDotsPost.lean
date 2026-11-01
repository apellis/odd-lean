/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.SectorDots
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.MixedInterchangePostPair
import OddMath.QuiverHecke.SwappedAssembly.QuadSame

/-! # The dot algebra on the first path of the mixed `iii` block `PRR`, `RPR`, `RRP`

For the relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, at `Eᵢ Eᵢ Eᵢ`, the paths with one probe summand and two reservoir summands
form the block `PRR`, `RPR`, `RRP` (`docs/Nondegeneracy/ThreeStrandSectorBraid.md`). It is
transported to the first path `PRR` by the mixed interchanges `Φ₁ = J : PRR ≅ RPR`
(`prrToRprIso`) and `Φ₂ = Φ₁ ≫ J : PRR ≅ RRP` (`prrToRrpIso`). On `PRR` there are the probe
dot `x` of the left letter (`prPreDot`), the reservoir dots `y`, `z` of the two right letters
(`prPostDot`, `prrPostDot`), the reservoir crossing `D` of the two right letters (`prrCross`),
and the transported mixed coefficients `δ = Φ₁ a Φ₁⁻¹` (`prrLeftCoeff`) and
`γ = Φ₂ a Φ₂⁻¹` (`prrRightCoeff`).

With `q = (-1)^{pᵢ}`:

* conjugation by `Φ₂` carries the probe and reservoir dots of `RRP` on its last two letters to
  `x` and `z` (`prrToRrpIso_conj_rpPreDot`, `prrToRrpIso_conj_rpPostDot`), and its reservoir
  crossing on the two left letters to `D` (`prrToRrpIso_conj_postCrossSame`, from (5B));
* conjugation by `Φ₁` carries the probe and reservoir dots of `RPR` on its first two letters
  to `q x` and `q y` (`prrToRprIso_conj_rpPreDot`, `prrToRprIso_conj_rpPostDot`);
* the dots and `D` supercommute with the colour sign, and `D` slides past `y`, `z`;
* hence `δ = a(q x, q y)` and `γ = a(x, z)` in the sense of `CrossCoeff.IsInverse`, and the
  odd denominators are units.

These are the inputs of `sectorRelations_even` and `sectorRelations_odd` for the block.
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

section Conj

variable {C : Type*} [Category C] [Preadditive C] {A A' : C}

omit [Preadditive C] in
private theorem conjPost_comp (φ : A ≅ A') (f g : A' ⟶ A') :
    φ.hom ≫ (f ≫ g) ≫ φ.inv = (φ.hom ≫ f ≫ φ.inv) ≫ (φ.hom ≫ g ≫ φ.inv) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem conjPost_sub (φ : A ≅ A') (f g : A' ⟶ A') :
    φ.hom ≫ (f - g) ≫ φ.inv = φ.hom ≫ f ≫ φ.inv - φ.hom ≫ g ≫ φ.inv := by
  simp only [Preadditive.sub_comp, Preadditive.comp_sub]

omit [Preadditive C] in
private theorem conjPost_id (φ : A ≅ A') : φ.hom ≫ 𝟙 A' ≫ φ.inv = 𝟙 A := by simp

private theorem conjPost_even (φ : A ≅ A') {a x y : A' ⟶ A'}
    (h : a ≫ (y - x) = 𝟙 _ ∧ (y - x) ≫ a = 𝟙 _) :
    (φ.hom ≫ a ≫ φ.inv) ≫ (φ.hom ≫ y ≫ φ.inv - φ.hom ≫ x ≫ φ.inv) = 𝟙 _ ∧
      (φ.hom ≫ y ≫ φ.inv - φ.hom ≫ x ≫ φ.inv) ≫ (φ.hom ≫ a ≫ φ.inv) = 𝟙 _ := by
  rw [← conjPost_sub, ← conjPost_comp, ← conjPost_comp, h.1, h.2, conjPost_id]
  exact ⟨rfl, rfl⟩

private theorem conjPost_odd (φ : A ≅ A') {a x y : A' ⟶ A'}
    (h : a ≫ (x ≫ x - y ≫ y) = x - y) :
    (φ.hom ≫ a ≫ φ.inv) ≫ ((φ.hom ≫ x ≫ φ.inv) ≫ (φ.hom ≫ x ≫ φ.inv) -
        (φ.hom ≫ y ≫ φ.inv) ≫ (φ.hom ≫ y ≫ φ.inv)) =
      φ.hom ≫ x ≫ φ.inv - φ.hom ≫ y ≫ φ.inv := by
  rw [← conjPost_comp, ← conjPost_comp, ← conjPost_sub, ← conjPost_comp, h, conjPost_sub]

private theorem conjPost_isUnit (φ : A ≅ A') {u : End A'} (h : IsUnit u) :
    IsUnit (M := End A) (φ.hom ≫ u ≫ φ.inv) :=
  h.map φ.symm.conj

variable {C' : Type*} [Category C'] [Preadditive C'] (F : C ⥤ C') [F.Additive]

private theorem mapPost_even {U : C} {a x y : U ⟶ U}
    (h : a ≫ (y - x) = 𝟙 _ ∧ (y - x) ≫ a = 𝟙 _) :
    F.map a ≫ (F.map y - F.map x) = 𝟙 _ ∧ (F.map y - F.map x) ≫ F.map a = 𝟙 _ := by
  rw [← F.map_sub, ← F.map_comp, ← F.map_comp, h.1, h.2, F.map_id]
  exact ⟨rfl, rfl⟩

private theorem mapPost_odd {U : C} {a x y : U ⟶ U} (h : a ≫ (x ≫ x - y ≫ y) = x - y) :
    F.map a ≫ (F.map x ≫ F.map x - F.map y ≫ F.map y) = F.map x - F.map y := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_sub, ← F.map_comp, h, F.map_sub]

end Conj

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- A relation `a = q • b` with `q = (-1)^{pp}` can be read backwards. -/
private theorem flip_koszul {C : Type*} [Category C] [Preadditive C] {A : C} (p : ZMod 2)
    {a b : A ⟶ A} (h : a = koszulSign p p • b) : b = koszulSign p p • a := by
  rw [h, smul_smul, koszulSign_mul_self, one_smul]

/-- At an odd colour the denominator `x² - y²` on a path `(R,P)` is a unit. -/
private theorem rpDenom_isUnit' (i : I) (h : P.CrossCoeffInputs) (hi : D.parity i = 1)
    (s : Sector I) (hv : StepValid (true, i) false s)
    (W : P.H (nextSector (true, i) true (nextSector (true, i) false s))) :
    IsUnit (M := End (P.rpObj i i s hv W))
      (P.rpPreDot i s hv W ≫ P.rpPreDot i s hv W -
        P.rpPostDot i s hv W ≫ P.rpPostDot i s hv W) := by
  have hne : D.parity i ≠ 0 := by rw [hi]; decide
  have hu := (P.crossDenom h i s hv W).isUnit
  simp only [crossDenom, hne, dite_false, IsUnit.unit_spec] at hu
  simpa only [pow_two, End.mul_def, sub_eq_add_neg] using hu

variable (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
  (hw : StepValid (true, i) false (nextSector (true, i) false t))
  (Z : P.H (nextSector (true, i) false (nextSector (true, i) false
    (nextSector (true, i) true t))))

/-- The two right letters `RR` of the path `PRR`, applied to `Z`. -/
abbrev prrRest : P.H (nextSector (true, i) false (nextSector (true, i) true t)) :=
  (P.step (true, i) false (nextSector (true, i) false (nextSector (true, i) true t)) hw).obj Z

/-- The last letter `P` of the path `RRP`, applied to `Z`. -/
abbrev prrTail : P.H (nextSector (true, i) false (nextSector (true, i) false t)) :=
  (P.step (true, i) true (nextSector (true, i) false (nextSector (true, i) false t)) trivial).obj Z

/-- The object of the first path `PRR`. -/
abbrev prrObj : P.H t := P.prObj i i t hv (P.prrRest i t hw Z)

/-- The interchange `Φ₁ = J` from the path `PRR` to the path `RPR` of `Eᵢ Eᵢ Eᵢ`. -/
def prrToRprIso : P.prrObj i t hv hw Z ≅ P.rpObj i i t hv (P.prrRest i t hw Z) :=
  P.mixedJ i i t hv (P.prrRest i t hw Z)

/-- The interchange `Φ₂ = Φ₁ ≫ J` from the path `PRR` to the path `RRP` of `Eᵢ Eᵢ Eᵢ`. -/
def prrToRrpIso :
    P.prrObj i t hv hw Z ≅
      (P.step (true, i) false t hv).obj (P.rpObj i i (nextSector (true, i) false t) hw Z) :=
  P.prrToRprIso i t hv hw Z ≪≫
    (P.step (true, i) false t hv).mapIso (P.mixedJ i i (nextSector (true, i) false t) hw Z)

/-- The reservoir dot `z` on the last letter of the path `PRR`. -/
def prrPostDot : End (P.prrObj i t hv hw Z) :=
  (P.step (true, i) true t trivial).map (P.rrRightDot i (nextSector (true, i) true t) hv hw Z)

/-- The reservoir crossing `D` of the two right letters of the path `PRR`. -/
def prrCross : End (P.prrObj i t hv hw Z) :=
  (P.step (true, i) true t trivial).map (P.postCrossSame i (nextSector (true, i) true t) hv hw Z)

/-- The mixed coefficient of the left crossing, transported to `PRR`: `δ = Φ₁ a Φ₁⁻¹`. -/
def prrLeftCoeff (c : P.CrossCoeff Sc) : End (P.prrObj i t hv hw Z) :=
  (P.prrToRprIso i t hv hw Z).hom ≫ c.a i t hv (P.prrRest i t hw Z) ≫
    (P.prrToRprIso i t hv hw Z).inv

/-- The mixed coefficient of the right crossing, transported to `PRR`: `γ = Φ₂ a Φ₂⁻¹`. -/
def prrRightCoeff (c : P.CrossCoeff Sc) : End (P.prrObj i t hv hw Z) :=
  (P.prrToRrpIso i t hv hw Z).hom ≫
    (P.step (true, i) false t hv).map (c.a i (nextSector (true, i) false t) hw Z) ≫
    (P.prrToRrpIso i t hv hw Z).inv

/-! ## Transport of the dots -/

/-- **`Φ₁` carries the probe dot of `RPR` to `q x`.** -/
theorem prrToRprIso_conj_rpPreDot :
    (P.prrToRprIso i t hv hw Z).hom ≫ P.rpPreDot i t hv (P.prrRest i t hw Z) ≫
        (P.prrToRprIso i t hv hw Z).inv =
      koszulSign (D.parity i) (D.parity i) • P.prPreDot i i t hv (P.prrRest i t hw Z) :=
  P.mixedJ_conj_rpPreDot i t hv _

/-- **`Φ₁` carries the reservoir dot of `RPR` on its first letter to `q y`.** -/
theorem prrToRprIso_conj_rpPostDot :
    (P.prrToRprIso i t hv hw Z).hom ≫ P.rpPostDot i t hv (P.prrRest i t hw Z) ≫
        (P.prrToRprIso i t hv hw Z).inv =
      koszulSign (D.parity i) (D.parity i) • P.prPostDot i i t hv (P.prrRest i t hw Z) :=
  P.mixedJ_conj_rpPostDot i t hv _

/-- The reservoir dot `z` passes through `Φ₁` with the colour sign, by supernaturality of the
mixed interchange. -/
theorem prrPostDot_comp_prrToRprIso :
    P.prrPostDot i t hv hw Z ≫ (P.prrToRprIso i t hv hw Z).hom =
      koszulSign (D.parity i) (D.parity i) • ((P.prrToRprIso i t hv hw Z).hom ≫
        (P.step (true, i) false t hv).map
          (P.prPostDot i i (nextSector (true, i) false t) hw Z)) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W i
    (nextSector (true, i) false (nextSector (true, i) true t)).1
    (P.muP (nextSector (true, i) false (nextSector (true, i) true t)))
    (P.muM_postE (t := nextSector (true, i) false (nextSector (true, i) true t)) i hw) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have h₀ := (P.mixedJ_supernatural i i t hv).naturality hθ
  rw [SKM.zmod2_mul_self, ← koszulSign_smul (R := k)] at h₀
  exact h₀

/-- Conjugation by `Φ₁` carries the reservoir dot of `RPR` on its last letter to `q z`. -/
theorem prrToRprIso_conj_map_prPostDot :
    (P.prrToRprIso i t hv hw Z).hom ≫
        (P.step (true, i) false t hv).map (P.prPostDot i i (nextSector (true, i) false t) hw Z) ≫
        (P.prrToRprIso i t hv hw Z).inv =
      koszulSign (D.parity i) (D.parity i) • P.prrPostDot i t hv hw Z := by
  have h := congrArg (· ≫ (P.prrToRprIso i t hv hw Z).inv)
    (P.prrPostDot_comp_prrToRprIso i t hv hw Z)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Linear.smul_comp] at h
  rw [h, smul_smul, koszulSign_mul_self, one_smul]

/-- **`Φ₂` carries the probe dot of `RRP` to `x`.** -/
theorem prrToRrpIso_conj_rpPreDot :
    (P.prrToRrpIso i t hv hw Z).hom ≫
        (P.step (true, i) false t hv).map
          (P.rpPreDot i (nextSector (true, i) false t) hw Z) ≫
        (P.prrToRrpIso i t hv hw Z).inv =
      P.prPreDot i i t hv (P.prrRest i t hw Z) := by
  have h : (P.step (true, i) false t hv).map
      ((P.mixedJ i i (nextSector (true, i) false t) hw Z).hom ≫
        P.rpPreDot i (nextSector (true, i) false t) hw Z ≫
        (P.mixedJ i i (nextSector (true, i) false t) hw Z).inv) =
      koszulSign (D.parity i) (D.parity i) • P.rpPreDot i t hv (P.prrRest i t hw Z) := by
    rw [P.mixedJ_conj_rpPreDot, Functor.map_zsmul]
    rfl
  simp only [prrToRrpIso, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, h, Linear.smul_comp,
    Linear.comp_smul, P.prrToRprIso_conj_rpPreDot, smul_smul, koszulSign_mul_self, one_smul]

/-- **`Φ₂` carries the reservoir dot of `RRP` on its middle letter to `z`.** -/
theorem prrToRrpIso_conj_rpPostDot :
    (P.prrToRrpIso i t hv hw Z).hom ≫
        (P.step (true, i) false t hv).map
          (P.rpPostDot i (nextSector (true, i) false t) hw Z) ≫
        (P.prrToRrpIso i t hv hw Z).inv =
      P.prrPostDot i t hv hw Z := by
  have h : (P.step (true, i) false t hv).map
      ((P.mixedJ i i (nextSector (true, i) false t) hw Z).hom ≫
        P.rpPostDot i (nextSector (true, i) false t) hw Z ≫
        (P.mixedJ i i (nextSector (true, i) false t) hw Z).inv) =
      koszulSign (D.parity i) (D.parity i) • (P.step (true, i) false t hv).map
        (P.prPostDot i i (nextSector (true, i) false t) hw Z) := by
    rw [P.mixedJ_conj_rpPostDot, Functor.map_zsmul]
  simp only [prrToRrpIso, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, h, Linear.smul_comp,
    Linear.comp_smul, P.prrToRprIso_conj_map_prPostDot, smul_smul, koszulSign_mul_self, one_smul]

/-- **(5B): `Φ₂` carries the reservoir crossing on the two left letters of `RRP` to `D`.** -/
theorem prrToRrpIso_conj_postCrossSame :
    (P.prrToRrpIso i t hv hw Z).hom ≫ P.postCrossSame i t hv hw (P.prrTail i t Z) ≫
        (P.prrToRrpIso i t hv hw Z).inv =
      P.prrCross i t hv hw Z := by
  rw [← Category.assoc, Iso.comp_inv_eq]
  simp only [prrToRrpIso, prrToRprIso, prrCross, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  exact (P.postCrossSame_mixedJ_pair i t hv hw Z).symm

/-! ## Supercommutation on the first path -/

/-- The probe dot of `PRR` supercommutes with any homogeneous endomorphism of parity `p` of
the two right letters. -/
private theorem prrPreDot_comp_map {Y Y' : P.H (nextSector (true, i) true t)} {p : ZMod 2}
    (θ : Y ⟶ Y') (hθ : θ ∈ parity (R := k) _ _ p) :
    P.T.dot i (P.muP_preE i t) ▷ Y ≫ (P.step (true, i) true t trivial).map θ =
      koszulSign (D.parity i) p •
        ((P.step (true, i) true t trivial).map θ ≫ P.T.dot i (P.muP_preE i t) ▷ Y') :=
  TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i _) hθ

/-- The reservoir dot `y` and the probe dot `x` of `PRR` supercommute. -/
theorem prPostDot_comp_prPreDot_prr :
    P.prPostDot i i t hv (P.prrRest i t hw Z) ≫ P.prPreDot i i t hv (P.prrRest i t hw Z) =
      koszulSign (D.parity i) (D.parity i) •
        (P.prPreDot i i t hv (P.prrRest i t hw Z) ≫
          P.prPostDot i i t hv (P.prrRest i t hw Z)) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W i
    (nextSector (true, i) true t).1 (P.muP (nextSector (true, i) true t))
    (P.muM_postE (t := nextSector (true, i) true t) i hv) 1).mem (P.prrRest i t hw Z)
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  exact flip_koszul _ (P.prrPreDot_comp_map i t _ hθ)

/-- The reservoir dot `z` and the probe dot `x` of `PRR` supercommute. -/
theorem prrPostDot_comp_prPreDot :
    P.prrPostDot i t hv hw Z ≫ P.prPreDot i i t hv (P.prrRest i t hw Z) =
      koszulSign (D.parity i) (D.parity i) •
        (P.prPreDot i i t hv (P.prrRest i t hw Z) ≫ P.prrPostDot i t hv hw Z) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W i
    (nextSector (true, i) false (nextSector (true, i) true t)).1
    (P.muP (nextSector (true, i) false (nextSector (true, i) true t)))
    (P.muM_postE (t := nextSector (true, i) false (nextSector (true, i) true t)) i hw) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have hθ' := IsSuperfunctor.map_mem (R := k)
    (F := P.step (true, i) false (nextSector (true, i) true t) hv) hθ
  exact flip_koszul _ (P.prrPreDot_comp_map i t _ hθ')

/-- The reservoir crossing `D` and the probe dot `x` of `PRR` supercommute. -/
theorem prrCross_comp_prPreDot :
    P.prrCross i t hv hw Z ≫ P.prPreDot i i t hv (P.prrRest i t hw Z) =
      koszulSign (D.parity i) (D.parity i) •
        (P.prPreDot i i t hv (P.prrRest i t hw Z) ≫ P.prrCross i t hv hw Z) := by
  have hθ := (P.postCrossSame_supernatural i (nextSector (true, i) true t) hv hw).mem Z
  have h := P.prrPreDot_comp_map i t _ hθ
  rw [SKM.zmod2_mul_self] at h
  exact flip_koszul _ h

/-- The two reservoir dots `z`, `y` of `PRR` supercommute. -/
theorem prrPostDot_comp_prPostDot :
    P.prrPostDot i t hv hw Z ≫ P.prPostDot i i t hv (P.prrRest i t hw Z) =
      koszulSign (D.parity i) (D.parity i) •
        (P.prPostDot i i t hv (P.prrRest i t hw Z) ≫ P.prrPostDot i t hv hw Z) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W i
    (nextSector (true, i) false (nextSector (true, i) true t)).1
    (P.muP (nextSector (true, i) false (nextSector (true, i) true t)))
    (P.muM_postE (t := nextSector (true, i) false (nextSector (true, i) true t)) i hw) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have hx := homContentPostDot_power_supernatural (k := k) P.T.obj P.W i
    (nextSector (true, i) true t).1 (P.muP (nextSector (true, i) true t))
    (P.muM_postE (t := nextSector (true, i) true t) i hv) 1
  simp only [Nat.cast_one, one_mul, pow_one] at hx
  have h₀ := hx.naturality hθ
  rw [← koszulSign_smul (R := k)] at h₀
  have h' := congrArg (P.step (true, i) true t trivial).map h₀
  simp only [Functor.map_comp, Functor.map_zsmul] at h'
  exact h'

/-- `D² = 0` on `PRR`. -/
theorem prrCross_sq : P.prrCross i t hv hw Z ≫ P.prrCross i t hv hw Z = 0 := by
  rw [prrCross, ← Functor.map_comp, P.postCrossSame_sq, Functor.map_zero]

/-- **The slides of `D` past the reservoir dots** `y`, `z` of `PRR`. -/
theorem prrCross_slides :
    (P.prPostDot i i t hv (P.prrRest i t hw Z) ≫ P.prrCross i t hv hw Z -
        koszulSign (D.parity i) (D.parity i) •
          (P.prrCross i t hv hw Z ≫ P.prrPostDot i t hv hw Z) = 𝟙 _) ∧
    (P.prrCross i t hv hw Z ≫ P.prPostDot i i t hv (P.prrRest i t hw Z) -
        koszulSign (D.parity i) (D.parity i) •
          (P.prrPostDot i t hv hw Z ≫ P.prrCross i t hv hw Z) = 𝟙 _) := by
  obtain ⟨h₁, h₂⟩ := P.postCrossSame_slides i (nextSector (true, i) true t) hv hw Z
  have h₁' := congrArg (P.step (true, i) true t trivial).map h₁
  have h₂' := congrArg (P.step (true, i) true t trivial).map h₂
  simp only [Functor.map_sub, Functor.map_comp, Functor.map_zsmul] at h₁' h₂'
  exact ⟨h₁'.trans (CategoryTheory.Functor.map_id _ _),
    h₂'.trans (CategoryTheory.Functor.map_id _ _)⟩

/-! ## The transported coefficients -/

private theorem prPreDot_eq_of_even (hi : D.parity i = 0) :
    P.prPreDot i i t hv (P.prrRest i t hw Z) =
      (P.prrToRprIso i t hv hw Z).hom ≫ P.rpPreDot i t hv (P.prrRest i t hw Z) ≫
        (P.prrToRprIso i t hv hw Z).inv := by
  rw [P.prrToRprIso_conj_rpPreDot, hi]
  simp [koszulSign]

private theorem prPostDot_eq_of_even (hi : D.parity i = 0) :
    P.prPostDot i i t hv (P.prrRest i t hw Z) =
      (P.prrToRprIso i t hv hw Z).hom ≫ P.rpPostDot i t hv (P.prrRest i t hw Z) ≫
        (P.prrToRprIso i t hv hw Z).inv := by
  rw [P.prrToRprIso_conj_rpPostDot, hi]
  simp [koszulSign]

private theorem prPreDot_eq_of_odd (hi : D.parity i = 1) :
    P.prPreDot i i t hv (P.prrRest i t hw Z) =
      -((P.prrToRprIso i t hv hw Z).hom ≫ P.rpPreDot i t hv (P.prrRest i t hw Z) ≫
        (P.prrToRprIso i t hv hw Z).inv) := by
  rw [P.prrToRprIso_conj_rpPreDot, hi]
  simp [koszulSign]

private theorem prPostDot_eq_of_odd (hi : D.parity i = 1) :
    P.prPostDot i i t hv (P.prrRest i t hw Z) =
      -((P.prrToRprIso i t hv hw Z).hom ≫ P.rpPostDot i t hv (P.prrRest i t hw Z) ≫
        (P.prrToRprIso i t hv hw Z).inv) := by
  rw [P.prrToRprIso_conj_rpPostDot, hi]
  simp [koszulSign]

/-- **`δ = a(x, y)` at an even colour**: `δ (y - x) = 1 = (y - x) δ`. -/
theorem prrLeftCoeff_even (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 0) :
    P.prrLeftCoeff i t hv hw Z c ≫ (P.prPostDot i i t hv (P.prrRest i t hw Z) -
        P.prPreDot i i t hv (P.prrRest i t hw Z)) = 𝟙 _ ∧
      (P.prPostDot i i t hv (P.prrRest i t hw Z) - P.prPreDot i i t hv (P.prrRest i t hw Z)) ≫
        P.prrLeftCoeff i t hv hw Z c = 𝟙 _ := by
  rw [P.prPostDot_eq_of_even i t hv hw Z hi, P.prPreDot_eq_of_even i t hv hw Z hi]
  exact conjPost_even _ (hc.even i hi t hv _)

/-- **`δ = a(-x, -y)` at an odd colour**: `δ (y² - x²) = x - y`. -/
theorem prrLeftCoeff_odd (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 1) :
    P.prrLeftCoeff i t hv hw Z c ≫
        (P.prPostDot i i t hv (P.prrRest i t hw Z) ≫ P.prPostDot i i t hv (P.prrRest i t hw Z) -
          P.prPreDot i i t hv (P.prrRest i t hw Z) ≫ P.prPreDot i i t hv (P.prrRest i t hw Z)) =
      P.prPreDot i i t hv (P.prrRest i t hw Z) - P.prPostDot i i t hv (P.prrRest i t hw Z) := by
  have h : P.prrLeftCoeff i t hv hw Z c ≫
        (P.prPreDot i i t hv (P.prrRest i t hw Z) ≫ P.prPreDot i i t hv (P.prrRest i t hw Z) -
          P.prPostDot i i t hv (P.prrRest i t hw Z) ≫
            P.prPostDot i i t hv (P.prrRest i t hw Z)) =
      P.prPostDot i i t hv (P.prrRest i t hw Z) - P.prPreDot i i t hv (P.prrRest i t hw Z) := by
    rw [P.prPostDot_eq_of_odd i t hv hw Z hi, P.prPreDot_eq_of_odd i t hv hw Z hi]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, sub_neg_eq_add,
      neg_add_eq_sub]
    exact conjPost_odd _ (hc.odd i hi t hv _).1
  rw [← neg_sub, Preadditive.comp_neg, h, neg_sub]

/-- **`γ = a(x, z)` at an even colour**: `γ (z - x) = 1 = (z - x) γ`. -/
theorem prrRightCoeff_even (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 0) :
    P.prrRightCoeff i t hv hw Z c ≫ (P.prrPostDot i t hv hw Z -
        P.prPreDot i i t hv (P.prrRest i t hw Z)) = 𝟙 _ ∧
      (P.prrPostDot i t hv hw Z - P.prPreDot i i t hv (P.prrRest i t hw Z)) ≫
        P.prrRightCoeff i t hv hw Z c = 𝟙 _ := by
  rw [← P.prrToRrpIso_conj_rpPostDot, ← P.prrToRrpIso_conj_rpPreDot]
  exact conjPost_even _ (mapPost_even _ (hc.even i hi (nextSector (true, i) false t) hw _))

/-- `γ (x² - z²) = x - z` at an odd colour. -/
private theorem prrRightCoeff_odd' (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (hi : D.parity i = 1) :
    P.prrRightCoeff i t hv hw Z c ≫
        (P.prPreDot i i t hv (P.prrRest i t hw Z) ≫ P.prPreDot i i t hv (P.prrRest i t hw Z) -
          P.prrPostDot i t hv hw Z ≫ P.prrPostDot i t hv hw Z) =
      P.prPreDot i i t hv (P.prrRest i t hw Z) - P.prrPostDot i t hv hw Z := by
  rw [← P.prrToRrpIso_conj_rpPostDot, ← P.prrToRrpIso_conj_rpPreDot]
  exact conjPost_odd _ (mapPost_odd _ (hc.odd i hi (nextSector (true, i) false t) hw _).1)

/-- **`γ = a(x, z)` at an odd colour**: `γ (z² - x²) = z - x`. -/
theorem prrRightCoeff_odd (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 1) :
    P.prrRightCoeff i t hv hw Z c ≫
        (P.prrPostDot i t hv hw Z ≫ P.prrPostDot i t hv hw Z -
          P.prPreDot i i t hv (P.prrRest i t hw Z) ≫ P.prPreDot i i t hv (P.prrRest i t hw Z)) =
      P.prrPostDot i t hv hw Z - P.prPreDot i i t hv (P.prrRest i t hw Z) := by
  rw [← neg_sub, Preadditive.comp_neg, P.prrRightCoeff_odd' i t hv hw Z c hc hi, neg_sub]

/-- **At an odd colour `z² - x²` is a unit.** -/
theorem prrRightDenom_isUnit (h : P.CrossCoeffInputs) (hi : D.parity i = 1) :
    IsUnit (M := End _) (P.prrPostDot i t hv hw Z ≫ P.prrPostDot i t hv hw Z -
      P.prPreDot i i t hv (P.prrRest i t hw Z) ≫ P.prPreDot i i t hv (P.prrRest i t hw Z)) := by
  rw [← neg_sub]
  refine IsUnit.neg ?_
  rw [← P.prrToRrpIso_conj_rpPostDot, ← P.prrToRrpIso_conj_rpPreDot, ← conjPost_comp,
    ← conjPost_comp, ← conjPost_sub, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_sub]
  exact conjPost_isUnit _ (((P.rpDenom_isUnit' i h hi (nextSector (true, i) false t) hw _).map
    ((P.step (true, i) false t hv).mapEnd (X := _))))

/-- **At an odd colour `y² - x²` is a unit.** -/
theorem prrLeftDenom_isUnit (h : P.CrossCoeffInputs) (hi : D.parity i = 1) :
    IsUnit (M := End _) (P.prPostDot i i t hv (P.prrRest i t hw Z) ≫
        P.prPostDot i i t hv (P.prrRest i t hw Z) -
      P.prPreDot i i t hv (P.prrRest i t hw Z) ≫ P.prPreDot i i t hv (P.prrRest i t hw Z)) := by
  rw [← neg_sub]
  refine IsUnit.neg ?_
  rw [P.prPostDot_eq_of_odd i t hv hw Z hi, P.prPreDot_eq_of_odd i t hv hw Z hi]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  rw [← conjPost_comp, ← conjPost_comp, ← conjPost_sub]
  exact conjPost_isUnit _ (P.rpDenom_isUnit' i h hi t hv _)

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
