/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SlideSame
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Cross
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.MixedInterchangePair

/-! # The dot algebra on the first path of a mixed `iii` block

For the relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, at `Eᵢ Eᵢ Eᵢ`, the block of paths `PPR`, `PRP`, `RPP` is transported to the
first path `PPR` by the mixed interchanges (`docs/Nondegeneracy/ThreeStrandSectorBraid.md`,
(1)): `Φ₁ = Eᵢ ◁ J : PPR ≅ PRP` (`pprToPrpIso`) and `Φ₂ = Φ₁ ≫ J : PPR ≅ RPP`
(`pprToRppIso`). On `PPR` there are the probe dots `x₁`, `x₂` of the two left letters
(`ppLeftDot`, `ppRightDot`), the reservoir dot `z` of the right letter (`pprPostDot`), the
probe crossing `D` of the two left letters (`preCrossSame`), and the transported mixed
coefficients `γ = Φ₂ a Φ₂⁻¹` (`pprLeftCoeff`) and `δ = Φ₁ a Φ₁⁻¹` (`pprRightCoeff`).

With `q = (-1)^{pᵢ}`:

* conjugation by `Φ₂` carries the probe and reservoir dots of `RPP` to `x₁` and `z`
  (`pprToRppIso_conj_rpPreDot`, `pprToRppIso_conj_rpPostDot`); conjugation by `Φ₁` carries
  those of `PRP` to `q x₂` and `q z` (`pprToPrpIso_conj_rpPreDot`,
  `pprToPrpIso_conj_rpPostDot`);
* the dots and `D` supercommute with the colour sign (`ppLeftDot_comp_ppRightDot`,
  `ppLeftDot_comp_pprPostDot`, `ppRightDot_comp_pprPostDot`, `preCrossSame_comp_pprPostDot`);
* hence `γ = a(x₁, z)` and `δ = a(q x₂, q z)` in the sense of `CrossCoeff.IsInverse`
  (`pprLeftCoeff_even`, `pprLeftCoeff_odd`, `pprRightCoeff_even`, `pprRightCoeff_odd`), and
  the odd denominators are units (`pprLeftDenom_isUnit`, `pprRightDenom_isUnit`).

These are the inputs of `sectorRelations_even` and `sectorRelations_odd`.
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
/-- Conjugation by an isomorphism respects composition. -/
private theorem conj_comp' (φ : A ≅ A') (f g : A' ⟶ A') :
    φ.hom ≫ (f ≫ g) ≫ φ.inv = (φ.hom ≫ f ≫ φ.inv) ≫ (φ.hom ≫ g ≫ φ.inv) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Conjugation by an isomorphism respects differences. -/
private theorem conj_sub' (φ : A ≅ A') (f g : A' ⟶ A') :
    φ.hom ≫ (f - g) ≫ φ.inv = φ.hom ≫ f ≫ φ.inv - φ.hom ≫ g ≫ φ.inv := by
  simp only [Preadditive.sub_comp, Preadditive.comp_sub]

omit [Preadditive C] in
/-- Conjugation by an isomorphism fixes the identity. -/
private theorem conj_id' (φ : A ≅ A') : φ.hom ≫ 𝟙 A' ≫ φ.inv = 𝟙 A := by simp

/-- The even identities of a coefficient pass through conjugation. -/
private theorem conj_even (φ : A ≅ A') {a x y : A' ⟶ A'}
    (h : a ≫ (y - x) = 𝟙 _ ∧ (y - x) ≫ a = 𝟙 _) :
    (φ.hom ≫ a ≫ φ.inv) ≫ (φ.hom ≫ y ≫ φ.inv - φ.hom ≫ x ≫ φ.inv) = 𝟙 _ ∧
      (φ.hom ≫ y ≫ φ.inv - φ.hom ≫ x ≫ φ.inv) ≫ (φ.hom ≫ a ≫ φ.inv) = 𝟙 _ := by
  rw [← conj_sub', ← conj_comp', ← conj_comp', h.1, h.2, conj_id']
  exact ⟨rfl, rfl⟩

/-- The odd identity of a coefficient passes through conjugation. -/
private theorem conj_odd (φ : A ≅ A') {a x y : A' ⟶ A'}
    (h : a ≫ (x ≫ x - y ≫ y) = x - y) :
    (φ.hom ≫ a ≫ φ.inv) ≫ ((φ.hom ≫ x ≫ φ.inv) ≫ (φ.hom ≫ x ≫ φ.inv) -
        (φ.hom ≫ y ≫ φ.inv) ≫ (φ.hom ≫ y ≫ φ.inv)) =
      φ.hom ≫ x ≫ φ.inv - φ.hom ≫ y ≫ φ.inv := by
  rw [← conj_comp', ← conj_comp', ← conj_sub', ← conj_comp', h, conj_sub']

/-- Conjugation by an isomorphism preserves units of the endomorphism ring. -/
private theorem conj_isUnit (φ : A ≅ A') {u : End A'} (h : IsUnit u) :
    IsUnit (M := End A) (φ.hom ≫ u ≫ φ.inv) :=
  h.map φ.symm.conj

variable {C' : Type*} [Category C'] [Preadditive C'] (F : C ⥤ C') [F.Additive]

/-- The even identities of a coefficient pass through an additive functor. -/
private theorem map_even {U : C} {a x y : U ⟶ U} (h : a ≫ (y - x) = 𝟙 _ ∧ (y - x) ≫ a = 𝟙 _) :
    F.map a ≫ (F.map y - F.map x) = 𝟙 _ ∧ (F.map y - F.map x) ≫ F.map a = 𝟙 _ := by
  rw [← F.map_sub, ← F.map_comp, ← F.map_comp, h.1, h.2, F.map_id]
  exact ⟨rfl, rfl⟩

/-- The odd identity of a coefficient passes through an additive functor. -/
private theorem map_odd {U : C} {a x y : U ⟶ U} (h : a ≫ (x ≫ x - y ≫ y) = x - y) :
    F.map a ≫ (F.map x ≫ F.map x - F.map y ≫ F.map y) = F.map x - F.map y := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_sub, ← F.map_comp, h, F.map_sub]

end Conj

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

private theorem shift_sum' (i : I) (β : I →₀ ℕ) :
    koszulSign (D.parity i)
        (homContentShift D i (β + Finsupp.single i 1) + homContentShift D i β) =
      koszulSign (D.parity i) (D.parity i) := by
  rw [homContentShift_add_single]
  congr 1
  generalize homContentShift D i β = a
  generalize D.parity i = p
  fin_cases a <;> fin_cases p <;> decide

/-! ## The mixed interchange conjugates the dots -/

/-- Conjugation by the mixed interchange carries the probe dot of `(R,P)` to `q` times that
of `(P,R)`. -/
@[reassoc]
theorem mixedJ_conj_rpPreDot (i : I) (s : Sector I)
    (hR : StepValid (true, i) false (nextSector (true, i) true s))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) true s))) :
    (P.mixedJ i i s hR Z).hom ≫ P.rpPreDot i s hR Z ≫ (P.mixedJ i i s hR Z).inv =
      koszulSign (D.parity i) (D.parity i) • P.prPreDot i i s hR Z := by
  have h := congrArg (· ≫ (P.mixedJ i i s hR Z).inv) (P.prPreDot_comp_mixedJ i s hR Z)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Linear.smul_comp] at h
  rw [h, smul_smul, koszulSign_mul_self, one_smul]

/-- Conjugation by the mixed interchange carries the reservoir dot of `(R,P)` to `q` times
that of `(P,R)`. -/
@[reassoc]
theorem mixedJ_conj_rpPostDot (i : I) (s : Sector I)
    (hR : StepValid (true, i) false (nextSector (true, i) true s))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) true s))) :
    (P.mixedJ i i s hR Z).hom ≫ P.rpPostDot i s hR Z ≫ (P.mixedJ i i s hR Z).inv =
      koszulSign (D.parity i) (D.parity i) • P.prPostDot i i s hR Z := by
  have h := congrArg (· ≫ (P.mixedJ i i s hR Z).inv) (P.prPostDot_comp_mixedJ i s hR Z)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Linear.smul_comp] at h
  rw [h, smul_smul, koszulSign_mul_self, one_smul]

/-! ## The first path of the block -/

variable (i : I) (t : Sector I)
  (hR : StepValid (true, i) false (nextSector (true, i) true (nextSector (true, i) true t)))
  (Z : P.H (nextSector (true, i) false
    (nextSector (true, i) true (nextSector (true, i) true t))))

/-- The interchange `Φ₁ = Eᵢ ◁ J` from the path `PPR` to the path `PRP` of `Eᵢ Eᵢ Eᵢ`. -/
def pprToPrpIso :
    (P.step (true, i) true t trivial).obj ((P.step (true, i) true _ trivial).obj
        ((P.step (true, i) false _ hR).obj Z)) ≅
      (P.step (true, i) true t trivial).obj
        ((P.step (true, i) false (nextSector (true, i) true t) hR).obj
          ((P.step (true, i) true (nextSector (true, i) false (nextSector (true, i) true t))
            trivial).obj Z)) :=
  (P.step (true, i) true t trivial).mapIso (P.mixedJ i i (nextSector (true, i) true t) hR Z)

/-- The interchange `Φ₂ = Φ₁ ≫ J` from the path `PPR` to the path `RPP` of `Eᵢ Eᵢ Eᵢ`. -/
def pprToRppIso :
    (P.step (true, i) true t trivial).obj ((P.step (true, i) true _ trivial).obj
        ((P.step (true, i) false _ hR).obj Z)) ≅
      P.rpObj i i t hR ((P.step (true, i) true
        (nextSector (true, i) false (nextSector (true, i) true t)) trivial).obj Z) :=
  P.pprToPrpIso i t hR Z ≪≫ P.mixedJ i i t hR ((P.step (true, i) true
        (nextSector (true, i) false (nextSector (true, i) true t)) trivial).obj Z)

/-- The reservoir dot `z` on the right letter of the path `PPR`. -/
def pprPostDot :
    End ((P.step (true, i) true t trivial).obj ((P.step (true, i) true _ trivial).obj
      ((P.step (true, i) false _ hR).obj Z))) :=
  (P.step (true, i) true t trivial).map (P.prPostDot i i (nextSector (true, i) true t) hR Z)

/-- The mixed coefficient of the left crossing, transported to `PPR`: `γ = Φ₂ a Φ₂⁻¹`. -/
def pprLeftCoeff (c : P.CrossCoeff Sc) :
    End ((P.step (true, i) true t trivial).obj ((P.step (true, i) true _ trivial).obj
      ((P.step (true, i) false _ hR).obj Z))) :=
  (P.pprToRppIso i t hR Z).hom ≫ c.a i t hR ((P.step (true, i) true
        (nextSector (true, i) false (nextSector (true, i) true t)) trivial).obj Z) ≫
    (P.pprToRppIso i t hR Z).inv

/-- The mixed coefficient of the right crossing, transported to `PPR`: `δ = Φ₁ a Φ₁⁻¹`. -/
def pprRightCoeff (c : P.CrossCoeff Sc) :
    End ((P.step (true, i) true t trivial).obj ((P.step (true, i) true _ trivial).obj
      ((P.step (true, i) false _ hR).obj Z))) :=
  (P.pprToPrpIso i t hR Z).hom ≫
    (P.step (true, i) true t trivial).map (c.a i (nextSector (true, i) true t) hR Z) ≫
    (P.pprToPrpIso i t hR Z).inv

/-- The outer probe dot of `PPR` supercommutes with any homogeneous endomorphism of parity
`p` of the two right letters. -/
private theorem ppLeftDot_comp_map {Y Y' : P.H (nextSector (true, i) true t)} {p : ZMod 2}
    (θ : Y ⟶ Y') (hθ : θ ∈ parity (R := k) _ _ p) :
    P.T.dot i (P.muP_preE i t) ▷ Y ≫ (P.step (true, i) true t trivial).map θ =
      koszulSign (D.parity i) p •
        ((P.step (true, i) true t trivial).map θ ≫ P.T.dot i (P.muP_preE i t) ▷ Y') :=
  TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i _) hθ

/-- The outer probe dot of `PPR` passes through `Φ₁` with the colour sign. -/
theorem ppLeftDot_comp_pprToPrpIso :
    P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) ≫ (P.pprToPrpIso i t hR Z).hom =
      koszulSign (D.parity i) (D.parity i) • ((P.pprToPrpIso i t hR Z).hom ≫
        P.prPreDot i i t hR ((P.step (true, i) true
        (nextSector (true, i) false (nextSector (true, i) true t)) trivial).obj Z)) := by
  have h := P.ppLeftDot_comp_map i t (P.mixedJ i i (nextSector (true, i) true t) hR Z).hom
    (homMixedInterchange_mem (k := k) _ _ _ _ _)
  have hs : koszulSign (D.parity i)
      (homContentShift D i (nextSector (true, i) true (nextSector (true, i) true t)).1 +
        homContentShift D i (nextSector (true, i) true t).1) =
      koszulSign (D.parity i) (D.parity i) := shift_sum' i _
  rw [hs] at h
  exact h

/-- Conjugation by `Φ₁` carries the outer probe dot of `PRP` to `q x₁`. -/
theorem pprToPrpIso_conj_prPreDot :
    (P.pprToPrpIso i t hR Z).hom ≫
        P.prPreDot i i t hR ((P.step (true, i) true
        (nextSector (true, i) false (nextSector (true, i) true t)) trivial).obj Z) ≫
        (P.pprToPrpIso i t hR Z).inv =
      koszulSign (D.parity i) (D.parity i) •
        P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) := by
  have h := congrArg (· ≫ (P.pprToPrpIso i t hR Z).inv) (P.ppLeftDot_comp_pprToPrpIso i t hR Z)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Linear.smul_comp] at h
  rw [h, smul_smul, koszulSign_mul_self, one_smul]

/-- **`Φ₂` carries the probe dot of `RPP` to `x₁`.** -/
theorem pprToRppIso_conj_rpPreDot :
    (P.pprToRppIso i t hR Z).hom ≫ P.rpPreDot i t hR ((P.step (true, i) true
        (nextSector (true, i) false (nextSector (true, i) true t)) trivial).obj Z) ≫
        (P.pprToRppIso i t hR Z).inv =
      P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) := by
  simp only [pprToRppIso, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [P.mixedJ_conj_rpPreDot_assoc, Linear.smul_comp, Linear.comp_smul,
    P.pprToPrpIso_conj_prPreDot, smul_smul, koszulSign_mul_self, one_smul]

/-- The reservoir dot of `PRP` on its right letter is the image of the reservoir dot of the
path `(R,P)` of the two right letters. -/
theorem prPostDot_eq_map_rpPostDot :
    P.prPostDot i i t hR ((P.step (true, i) true
        (nextSector (true, i) false (nextSector (true, i) true t)) trivial).obj Z) =
      (P.step (true, i) true t trivial).map (P.rpPostDot i (nextSector (true, i) true t) hR Z) :=
  rfl

/-- **`Φ₁` carries the probe dot of `PRP` on its middle letter to `q x₂`.** -/
theorem pprToPrpIso_conj_rpPreDot :
    (P.pprToPrpIso i t hR Z).hom ≫
        (P.step (true, i) true t trivial).map (P.rpPreDot i (nextSector (true, i) true t) hR Z) ≫
        (P.pprToPrpIso i t hR Z).inv =
      koszulSign (D.parity i) (D.parity i) •
        P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) := by
  simp only [pprToPrpIso, Functor.mapIso_hom, Functor.mapIso_inv, ← Functor.map_comp,
    P.mixedJ_conj_rpPreDot]
  rw [Functor.map_zsmul]
  rfl

/-- **`Φ₁` carries the reservoir dot of `PRP` to `q z`.** -/
theorem pprToPrpIso_conj_rpPostDot :
    (P.pprToPrpIso i t hR Z).hom ≫
        (P.step (true, i) true t trivial).map (P.rpPostDot i (nextSector (true, i) true t) hR Z) ≫
        (P.pprToPrpIso i t hR Z).inv =
      koszulSign (D.parity i) (D.parity i) • P.pprPostDot i t hR Z := by
  simp only [pprToPrpIso, Functor.mapIso_hom, Functor.mapIso_inv, ← Functor.map_comp,
    P.mixedJ_conj_rpPostDot]
  rw [Functor.map_zsmul]
  rfl

/-- **`Φ₂` carries the reservoir dot of `RPP` to `z`.** -/
theorem pprToRppIso_conj_rpPostDot :
    (P.pprToRppIso i t hR Z).hom ≫ P.rpPostDot i t hR ((P.step (true, i) true
        (nextSector (true, i) false (nextSector (true, i) true t)) trivial).obj Z) ≫
        (P.pprToRppIso i t hR Z).inv =
      P.pprPostDot i t hR Z := by
  simp only [pprToRppIso, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [P.mixedJ_conj_rpPostDot_assoc, Linear.smul_comp, Linear.comp_smul,
    P.prPostDot_eq_map_rpPostDot, P.pprToPrpIso_conj_rpPostDot, smul_smul, koszulSign_mul_self,
    one_smul]

/-! ## Supercommutation on the first path -/

/-- The two probe dots of `PPR` supercommute. -/
theorem ppLeftDot_comp_ppRightDot :
    P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) ≫
        P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) =
      koszulSign (D.parity i) (D.parity i) •
        (P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) ≫
          P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z)) :=
  P.ppLeftDot_comp_map i t _ (TwoSupercategory.whiskerRight_mem _ (P.T.dot_mem i _))

/-- The outer probe dot and the reservoir dot of `PPR` supercommute. -/
theorem ppLeftDot_comp_pprPostDot :
    P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) ≫ P.pprPostDot i t hR Z =
      koszulSign (D.parity i) (D.parity i) •
        (P.pprPostDot i t hR Z ≫ P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z)) :=
  P.ppLeftDot_comp_map i t _
    ((P.prPostDot_supernatural i i (nextSector (true, i) true t) hR).mem Z)

/-- The inner probe dot and the reservoir dot of `PPR` supercommute. -/
theorem ppRightDot_comp_pprPostDot :
    P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) ≫ P.pprPostDot i t hR Z =
      koszulSign (D.parity i) (D.parity i) •
        (P.pprPostDot i t hR Z ≫ P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z)) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W i
    (nextSector (true, i) true (nextSector (true, i) true t)).1
    (P.muP (nextSector (true, i) true (nextSector (true, i) true t))) (P.muM_postE i hR) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have h := P.ppLeftDot_comp_map i (nextSector (true, i) true t) _ hθ
  have h' := congrArg (P.step (true, i) true t trivial).map h
  simp only [Functor.map_comp, Functor.map_zsmul] at h'
  exact h'

/-- The probe crossing and the reservoir dot of `PPR` supercommute. -/
theorem preCrossSame_comp_pprPostDot :
    P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z) ≫ P.pprPostDot i t hR Z =
      koszulSign (D.parity i) (D.parity i) •
        (P.pprPostDot i t hR Z ≫ P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z)) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W i
    (nextSector (true, i) true (nextSector (true, i) true t)).1
    (P.muP (nextSector (true, i) true (nextSector (true, i) true t))) (P.muM_postE i hR) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have h : P.pprPostDot i t hR Z ≫ P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z) =
      koszulSign (D.parity i) (D.parity i) •
        (P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z) ≫ P.pprPostDot i t hR Z) := by
    have h₀ := (P.preCrossSame_supernatural i t).naturality hθ
    rw [SKM.zmod2_mul_self, ← koszulSign_smul (R := k)] at h₀
    exact h₀
  rw [h, smul_smul, koszulSign_mul_self, one_smul]

/-! ## The transported coefficients -/

/-- **`γ = a(x₁, z)` at an even colour**: `γ (z - x₁) = 1 = (z - x₁) γ`. -/
theorem pprLeftCoeff_even (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 0) :
    P.pprLeftCoeff i t hR Z c ≫ (P.pprPostDot i t hR Z -
        P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z)) = 𝟙 _ ∧
      (P.pprPostDot i t hR Z - P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z)) ≫
        P.pprLeftCoeff i t hR Z c = 𝟙 _ := by
  rw [← P.pprToRppIso_conj_rpPostDot, ← P.pprToRppIso_conj_rpPreDot]
  exact conj_even _ (hc.even i hi t hR _)

/-- **`γ = a(x₁, z)` at an odd colour**: `γ (x₁² - z²) = x₁ - z`. -/
theorem pprLeftCoeff_odd (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 1) :
    P.pprLeftCoeff i t hR Z c ≫
        (P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) ≫
            P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) -
          P.pprPostDot i t hR Z ≫ P.pprPostDot i t hR Z) =
      P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) - P.pprPostDot i t hR Z := by
  rw [← P.pprToRppIso_conj_rpPostDot, ← P.pprToRppIso_conj_rpPreDot]
  exact conj_odd _ (hc.odd i hi t hR _).1

/-- The probe dot `x₂` at an even colour, as the transported probe dot of `PRP`. -/
private theorem ppRightDot_eq_of_even (hi : D.parity i = 0) :
    P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) =
      (P.pprToPrpIso i t hR Z).hom ≫
        (P.step (true, i) true t trivial).map (P.rpPreDot i (nextSector (true, i) true t) hR Z) ≫
        (P.pprToPrpIso i t hR Z).inv := by
  rw [P.pprToPrpIso_conj_rpPreDot, hi]
  simp [koszulSign]

/-- The reservoir dot `z` at an even colour, as the transported reservoir dot of `PRP`. -/
private theorem pprPostDot_eq_of_even (hi : D.parity i = 0) :
    P.pprPostDot i t hR Z =
      (P.pprToPrpIso i t hR Z).hom ≫
        (P.step (true, i) true t trivial).map (P.rpPostDot i (nextSector (true, i) true t) hR Z) ≫
        (P.pprToPrpIso i t hR Z).inv := by
  rw [P.pprToPrpIso_conj_rpPostDot, hi]
  simp [koszulSign]

/-- The probe dot `x₂` at an odd colour, as minus the transported probe dot of `PRP`. -/
private theorem ppRightDot_eq_of_odd (hi : D.parity i = 1) :
    P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) =
      -((P.pprToPrpIso i t hR Z).hom ≫
        (P.step (true, i) true t trivial).map (P.rpPreDot i (nextSector (true, i) true t) hR Z) ≫
        (P.pprToPrpIso i t hR Z).inv) := by
  rw [P.pprToPrpIso_conj_rpPreDot, hi]
  simp [koszulSign]

/-- The reservoir dot `z` at an odd colour, as minus the transported reservoir dot of `PRP`. -/
private theorem pprPostDot_eq_of_odd (hi : D.parity i = 1) :
    P.pprPostDot i t hR Z =
      -((P.pprToPrpIso i t hR Z).hom ≫
        (P.step (true, i) true t trivial).map (P.rpPostDot i (nextSector (true, i) true t) hR Z) ≫
        (P.pprToPrpIso i t hR Z).inv) := by
  rw [P.pprToPrpIso_conj_rpPostDot, hi]
  simp [koszulSign]

/-- **`δ = a(x₂, z)` at an even colour**: `δ (z - x₂) = 1 = (z - x₂) δ`. -/
theorem pprRightCoeff_even (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 0) :
    P.pprRightCoeff i t hR Z c ≫ (P.pprPostDot i t hR Z -
        P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z)) = 𝟙 _ ∧
      (P.pprPostDot i t hR Z - P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z)) ≫
        P.pprRightCoeff i t hR Z c = 𝟙 _ := by
  rw [P.pprPostDot_eq_of_even i t hR Z hi, P.ppRightDot_eq_of_even i t hR Z hi]
  exact conj_even _ (map_even _ (hc.even i hi (nextSector (true, i) true t) hR Z))

/-- **`δ = a(-x₂, -z)` at an odd colour**: `δ (x₂² - z²) = z - x₂`. -/
theorem pprRightCoeff_odd (c : P.CrossCoeff Sc) (hc : c.IsInverse) (hi : D.parity i = 1) :
    P.pprRightCoeff i t hR Z c ≫
        (P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) ≫
            P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) -
          P.pprPostDot i t hR Z ≫ P.pprPostDot i t hR Z) =
      P.pprPostDot i t hR Z - P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) := by
  rw [P.pprPostDot_eq_of_odd i t hR Z hi, P.ppRightDot_eq_of_odd i t hR Z hi]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, sub_neg_eq_add,
    neg_add_eq_sub]
  exact conj_odd _ (map_odd _ (hc.odd i hi (nextSector (true, i) true t) hR Z).1)

/-- At an odd colour the denominator `x² - y²` on a path `(R,P)` is a unit. -/
private theorem rpDenom_isUnit (h : P.CrossCoeffInputs) (hi : D.parity i = 1) (s : Sector I)
    (hv : StepValid (true, i) false s)
    (W : P.H (nextSector (true, i) true (nextSector (true, i) false s))) :
    IsUnit (M := End (P.rpObj i i s hv W))
      (P.rpPreDot i s hv W ≫ P.rpPreDot i s hv W -
        P.rpPostDot i s hv W ≫ P.rpPostDot i s hv W) := by
  have hne : D.parity i ≠ 0 := by rw [hi]; decide
  have hu := (P.crossDenom h i s hv W).isUnit
  simp only [crossDenom, hne, dite_false, IsUnit.unit_spec] at hu
  simpa only [pow_two, End.mul_def, sub_eq_add_neg] using hu

/-- **At an odd colour `x₁² - z²` is a unit.** -/
theorem pprLeftDenom_isUnit (h : P.CrossCoeffInputs) (hi : D.parity i = 1) :
    IsUnit (M := End _) (P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) ≫
        P.ppLeftDot i t ((P.step (true, i) false _ hR).obj Z) -
      P.pprPostDot i t hR Z ≫ P.pprPostDot i t hR Z) := by
  rw [← P.pprToRppIso_conj_rpPostDot, ← P.pprToRppIso_conj_rpPreDot, ← conj_comp',
    ← conj_comp', ← conj_sub']
  exact conj_isUnit _ (P.rpDenom_isUnit i h hi t hR _)

/-- **At an odd colour `x₂² - z²` is a unit.** -/
theorem pprRightDenom_isUnit (h : P.CrossCoeffInputs) (hi : D.parity i = 1) :
    IsUnit (M := End _) (P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) ≫
        P.ppRightDot i t ((P.step (true, i) false _ hR).obj Z) -
      P.pprPostDot i t hR Z ≫ P.pprPostDot i t hR Z) := by
  rw [P.pprPostDot_eq_of_odd i t hR Z hi, P.ppRightDot_eq_of_odd i t hR Z hi]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  rw [← conj_comp', ← conj_comp', ← conj_sub', ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_sub]
  exact conj_isUnit _ (((P.rpDenom_isUnit i h hi (nextSector (true, i) true t) hR Z).map
    ((P.step (true, i) true t trivial).mapEnd (X := _))))

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
