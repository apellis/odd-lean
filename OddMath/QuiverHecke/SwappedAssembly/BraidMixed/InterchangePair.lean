/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.MixedInterchangePair

/-! # Mixed interchange triangles for two probe colours

The two-probe triangle in `docs/Nondegeneracy/MixedColourRemainingBraid.md` §2,
proved from the super-interchange law of Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, §1, and the parity of the crossing in
Definition 1.5. This is a constituent of (1.9), not the full braid relation.

The source and target pairs may have different intermediate objects. Their
intermediate shifts may differ, and the outer shifts need not agree. The
signed identity retains both outer-shift signs. At the content shifts of a
factor crossing their product is one, since `(p_i + p_j) p_i p_j = 0`.
No crossing or parameter polynomial is inverted. The result applies to
repeated as well as distinct colours and does not change any generator.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b b' c d e : B}

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
include k in
/-- Reassociation of a map between two possibly different two-letter paths. -/
@[reassoc]
theorem pairAssociator_whiskerRight_between (E₁ : a ⟶ b) (E₂ : b ⟶ c)
    (E₁' : a ⟶ b') (E₂' : b' ⟶ c) (Z : c ⟶ d) (F : d ⟶ e)
    (η : E₁ ≫ E₂ ⟶ E₁' ≫ E₂') :
    (associator E₁ E₂ (Z ≫ F)).inv ≫ η ▷ (Z ≫ F) ≫
        (associator E₁' E₂' (Z ≫ F)).hom ≫
        E₁' ◁ (associator E₂' Z F).inv ≫ (associator E₁' (E₂' ≫ Z) F).inv =
      E₁ ◁ (associator E₂ Z F).inv ≫ (associator E₁ (E₂ ≫ Z) F).inv ≫
        ((associator E₁ E₂ Z).inv ≫ η ▷ Z ≫ (associator E₁' E₂' Z).hom) ▷ F := by
  have hp (G₁ : a ⟶ b') (G₂ : b' ⟶ c) :
      G₁ ◁ (associator G₂ Z F).inv ≫ (associator G₁ (G₂ ≫ Z) F).inv =
      (associator G₁ G₂ (Z ≫ F)).inv ≫ (associator (G₁ ≫ G₂) Z F).inv ≫
        (associator G₁ G₂ Z).hom ▷ F := by
    rw [← TwoSupercategory.pentagon_inv_assoc (R := k)]
    simp only [TwoSupercategory.inv_hom_whiskerRight (R := k), Category.comp_id]
  rw [hp, Iso.hom_inv_id_assoc, TwoSupercategory.associator_inv_naturality_left_assoc (R := k),
    TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.comp_whiskerRight (R := k)]
  rw [TwoSupercategory.pentagon_inv_assoc (R := k)]

/-- The inner parity shifts cancel even when the two outer shifts differ. -/
theorem homMixedInterchange_pair_shifts (E₁ : a ⟶ b) (E₂ : b ⟶ c) (Z : c ⟶ d)
    (F : d ⟶ e) (κ τ ρ : ZMod 2) :
    E₁ ◁ (homMixedInterchange (k := k) E₂ F κ τ Z).hom ≫
        (homMixedInterchange (k := k) E₁ F τ ρ (E₂ ≫ Z)).hom =
      E₁ ◁ E₂ ◁ ((homParityShiftDatum (k := k) κ).iso (Z ≫ F)).hom ≫
        E₁ ◁ (associator E₂ Z F).inv ≫ (associator E₁ (E₂ ≫ Z) F).inv ≫
          ((homParityShiftDatum (k := k) ρ).iso ((E₁ ≫ E₂ ≫ Z) ≫ F)).inv := by
  simp only [homMixedInterchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, homPre,
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc,
    TwoSupercategory.whiskerLeft_inv_hom_assoc (R := k)]

/-- A homogeneous map passes through the pair of mixed interchanges with the
product of the source-removal and target-insertion Koszul signs. -/
theorem homMixedInterchange_pair_cross (E₁ : a ⟶ b) (E₂ : b ⟶ c)
    (E₁' : a ⟶ b') (E₂' : b' ⟶ c) (Z : c ⟶ d) (F : d ⟶ e)
    (κ τ τ' ρ : ZMod 2) {p : ZMod 2} {η : E₁ ≫ E₂ ⟶ E₁' ≫ E₂'}
    (hη : η ∈ parity (R := k) _ _ p) :
    ((associator E₁ E₂ ((homParityShift (k := k) κ).obj (Z ≫ F))).inv ≫
        η ▷ (homParityShift (k := k) κ).obj (Z ≫ F) ≫
          (associator E₁' E₂' ((homParityShift (k := k) κ).obj (Z ≫ F))).hom) ≫
        E₁' ◁ (homMixedInterchange (k := k) E₂' F κ τ' Z).hom ≫
          (homMixedInterchange (k := k) E₁' F τ' ρ (E₂' ≫ Z)).hom =
      (koszulSign p κ * koszulSign ρ p) •
        (E₁ ◁ (homMixedInterchange (k := k) E₂ F κ τ Z).hom ≫
          (homMixedInterchange (k := k) E₁ F τ ρ (E₂ ≫ Z)).hom ≫
            (homParityShift (k := k) ρ).map
              (((associator E₁ E₂ Z).inv ≫ η ▷ Z ≫ (associator E₁' E₂' Z).hom) ▷ F)) := by
  rw [homMixedInterchange_pair_shifts,
    ← Category.assoc (E₁ ◁ _), homMixedInterchange_pair_shifts]
  simp only [Category.assoc]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k),
    TwoSupercategory.super_interchange_assoc (R := k) hη
      ((homParityShiftDatum (k := k) κ).hom_mem _),
    Linear.comp_smul, ← TwoSupercategory.associator_inv_naturality_right_assoc (R := k),
    pairAssociator_whiskerRight_between_assoc (k := k)]
  have hθ : ((associator E₁ E₂ Z).inv ≫ η ▷ Z ≫ (associator E₁' E₂' Z).hom) ▷ F ∈
      parity (R := k) _ _ p := by
    refine TwoSupercategory.whiskerRight_mem F ?_
    simpa only [zero_add, add_zero, Category.assoc] using comp_mem
      (comp_mem (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ Z))
        (TwoSupercategory.whiskerRight_mem Z hη))
      (TwoSupercategory.associator_hom_mem (R := k) E₁' E₂' Z)
  rw [(homParityShiftDatum (k := k) ρ).inv_naturality hθ]
  simp only [Linear.comp_smul, smul_smul, ← koszulSign_smul (R := k)]

section Content
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- The outer-shift signs cancel for the parity of a two-colour crossing. -/
theorem homContentShift_pair_cross_sign (i j r : I) (β : I →₀ ℕ) :
    koszulSign (D.parity i * D.parity j)
        (homContentShift D r (β + Finsupp.single j 1 + Finsupp.single i 1)) *
      koszulSign (homContentShift D r β) (D.parity i * D.parity j) = 1 := by
  rw [homContentShift_add_single, homContentShift_add_single]
  generalize homContentShift D r β = b
  generalize D.parity i = pi
  generalize D.parity j = pj
  generalize D.parity r = pr
  fin_cases b <;> fin_cases pi <;> fin_cases pj <;> fin_cases pr <;> decide

/-- The two-probe, one-reservoir interchange triangle for the factor crossing,
with the content shifts of all three sectors. No colour inequality is required. -/
theorem RouquierData.cross_mixedInterchange_pair (T : RouquierData (k := k) (B := B) D)
    (i j r : I) (β : I →₀ ℕ) {a₀ a₁ a₁' a₂ : X}
    (h₁ : a₀ + D.α j = a₁) (h₂ : a₁ + D.α i = a₂)
    (h₃ : a₀ + D.α i = a₁') (h₄ : a₁' + D.α j = a₂)
    {d e : B} (Z : T.obj a₂ ⟶ d) (F : d ⟶ e) :
    let κ := homContentShift D r (β + Finsupp.single j 1 + Finsupp.single i 1)
    let τ := homContentShift D r (β + Finsupp.single j 1)
    let τ' := homContentShift D r (β + Finsupp.single i 1)
    let ρ := homContentShift D r β
    ((associator (T.E j h₁) (T.E i h₂) ((homParityShift (k := k) κ).obj (Z ≫ F))).inv ≫
        T.cross i j h₁ h₂ h₃ h₄ ▷ (homParityShift (k := k) κ).obj (Z ≫ F) ≫
          (associator (T.E i h₃) (T.E j h₄) ((homParityShift (k := k) κ).obj (Z ≫ F))).hom) ≫
        T.E i h₃ ◁ (homMixedInterchange (k := k) (T.E j h₄) F κ τ' Z).hom ≫
          (homMixedInterchange (k := k) (T.E i h₃) F τ' ρ (T.E j h₄ ≫ Z)).hom =
      T.E j h₁ ◁ (homMixedInterchange (k := k) (T.E i h₂) F κ τ Z).hom ≫
        (homMixedInterchange (k := k) (T.E j h₁) F τ ρ (T.E i h₂ ≫ Z)).hom ≫
          (homParityShift (k := k) ρ).map
            (((associator (T.E j h₁) (T.E i h₂) Z).inv ≫ T.cross i j h₁ h₂ h₃ h₄ ▷ Z ≫
              (associator (T.E i h₃) (T.E j h₄) Z).hom) ▷ F) := by
  dsimp only
  rw [homMixedInterchange_pair_cross _ _ _ _ _ _ _ _ _ _ (T.cross_mem i j h₁ h₂ h₃ h₄),
    homContentShift_pair_cross_sign, one_smul]
end Content
end OddMath.SKM
