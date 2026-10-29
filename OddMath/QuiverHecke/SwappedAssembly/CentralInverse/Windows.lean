/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals

/-! # Window identities for the probe slide

This file proves the window identities (4) of `docs/Nondegeneracy/ProbeWindowInverse.md`
in an abstract preadditive category. They are the first step of the inversion of the
central block of the equal-colour augmented maps (`SwappedHomInversion.md`, §§5–6, and
`AugmentedSectorBlocks.md`, §3), whose entries come from the slide relation of the
Rouquier mate in Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
(1.13)–(1.14).

Data: objects `X`, `Y`, `O`, a map `s : X ⟶ Y`, automorphisms `x` of `X` and `y` of `Y`,
maps `v : X ⟶ O`, `u : O ⟶ Y` and a sign `q` with `q * q = 1`, satisfying the slide
(in execution order)

    s ≫ y - q • (x ≫ s) = v ≫ u.

With `u_r = u ≫ yʳ` and `v_n = xⁿ ≫ v` (negative powers through the inverse
automorphisms) the identities are, for every `l : ℕ`,

    s + Σ_{r<l} q^(r+1) • (v_{-r-1} ≫ u_r) = q^l • (x^{-l} ≫ s ≫ y^l),
    s - Σ_{r<l} q^(r+2) • (v_r ≫ u_{-r-1}) = q^l • (x^l ≫ s ≫ y^{-l})

(`ProbeWindow.window_neg`, `ProbeWindow.window_pos`). They use only the slide and the
inverse identities of the dots.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory

variable {C : Type*} [Category C]

private lemma inv_hom_comp_hom {Z : C} (a : Aut Z) : (a⁻¹).hom ≫ a.hom = 𝟙 Z := a.inv_hom_id

private lemma hom_comp_inv_hom {Z : C} (a : Aut Z) : a.hom ≫ (a⁻¹).hom = 𝟙 Z := a.hom_inv_id

private lemma one_hom {Z : C} : (1 : Aut Z).hom = 𝟙 Z := rfl

private lemma pow_succ_hom' {Z : C} (a : Aut Z) (l : ℕ) :
    (a ^ (l + 1)).hom = (a ^ l).hom ≫ a.hom := by
  rw [pow_succ', Aut.Aut_mul_def]; rfl

private lemma pow_succ_hom {Z : C} (a : Aut Z) (l : ℕ) :
    (a ^ (l + 1)).hom = a.hom ≫ (a ^ l).hom := by
  rw [pow_succ, Aut.Aut_mul_def]; rfl

variable [Preadditive C] {X Y O : C}

/-- The first window identity of `ProbeWindowInverse.md` (4): conjugating `s` by `l`
negative probe-dot powers on the source and `l` positive powers on the target. -/
theorem window_neg (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O) (u : O ⟶ Y) (q : ℤ)
    (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u) (l : ℕ) :
    s + ∑ r ∈ Finset.range l,
        q ^ (r + 1) • (((x⁻¹) ^ (r + 1)).hom ≫ v ≫ u ≫ (y ^ r).hom) =
      q ^ l • (((x⁻¹) ^ l).hom ≫ s ≫ (y ^ l).hom) := by
  have hmid : (x⁻¹).hom ≫ s ≫ y.hom = q • s + (x⁻¹).hom ≫ v ≫ u := by
    have : s ≫ y.hom = q • (x.hom ≫ s) + v ≫ u := by rw [← hslide]; abel
    rw [this, Preadditive.comp_add, Preadditive.comp_zsmul, ← Category.assoc,
      inv_hom_comp_hom, Category.id_comp]
  induction l with
  | zero => simp [one_hom]
  | succ l ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, pow_succ_hom' (x⁻¹) l, pow_succ_hom y l]
    have hmid' : (x⁻¹).hom ≫ s ≫ y.hom ≫ (y ^ l).hom =
        q • (s ≫ (y ^ l).hom) + (x⁻¹).hom ≫ v ≫ u ≫ (y ^ l).hom := by
      simpa only [Category.assoc, Preadditive.add_comp, Preadditive.zsmul_comp] using
        congrArg (· ≫ (y ^ l).hom) hmid
    simp only [Category.assoc]
    rw [hmid', Preadditive.comp_add,
      Preadditive.comp_zsmul, smul_add, smul_smul]
    have hq2 : q ^ (l + 1) * q = q ^ l := by
      rw [pow_succ, mul_assoc, hq, mul_one]
    rw [hq2]

/-- The second window identity of `ProbeWindowInverse.md` (4): conjugating `s` by `l`
positive probe-dot powers on the source and `l` negative powers on the target. -/
theorem window_pos (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O) (u : O ⟶ Y) (q : ℤ)
    (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u) (l : ℕ) :
    s - ∑ r ∈ Finset.range l,
        q ^ (r + 2) • ((x ^ r).hom ≫ v ≫ u ≫ ((y⁻¹) ^ (r + 1)).hom) =
      q ^ l • ((x ^ l).hom ≫ s ≫ ((y⁻¹) ^ l).hom) := by
  have hmid : x.hom ≫ s ≫ (y⁻¹).hom = q • s - q • (v ≫ u ≫ (y⁻¹).hom) := by
    have h1 : s = q • (x.hom ≫ s ≫ (y⁻¹).hom) + v ≫ u ≫ (y⁻¹).hom := by
      have h2 : s ≫ y.hom ≫ (y⁻¹).hom = s := by
        rw [hom_comp_inv_hom, Category.comp_id]
      have : s ≫ y.hom = q • (x.hom ≫ s) + v ≫ u := by rw [← hslide]; abel
      conv_lhs => rw [← h2, ← Category.assoc, this]
      rw [Preadditive.add_comp, Preadditive.zsmul_comp]
      simp only [Category.assoc]
    conv_rhs => rw [h1]
    rw [smul_add, smul_smul, hq, one_smul]
    abel
  induction l with
  | zero => simp [one_hom]
  | succ l ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih, pow_succ_hom' x l, pow_succ_hom (y⁻¹) l]
    have hmid' : x.hom ≫ s ≫ (y⁻¹).hom ≫ ((y⁻¹) ^ l).hom =
        q • (s ≫ ((y⁻¹) ^ l).hom) - q • (v ≫ u ≫ (y⁻¹).hom ≫ ((y⁻¹) ^ l).hom) := by
      simpa only [Category.assoc, Preadditive.sub_comp, Preadditive.zsmul_comp] using
        congrArg (· ≫ ((y⁻¹) ^ l).hom) hmid
    simp only [Category.assoc]
    rw [hmid', Preadditive.comp_sub, Preadditive.comp_zsmul, Preadditive.comp_zsmul, smul_sub,
      smul_smul, smul_smul]
    have hq2 : q ^ (l + 1) * q = q ^ l := by
      rw [pow_succ, mul_assoc, hq, mul_one]
    have hq3 : q ^ (l + 1) * q = q ^ (l + 2) := by ring
    have hq4 : q ^ (l + 2) = q ^ l := by rw [← hq3, hq2]
    rw [hq2, hq4]

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
