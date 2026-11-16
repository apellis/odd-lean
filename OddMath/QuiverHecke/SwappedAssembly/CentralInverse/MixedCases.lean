/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.BlockMaps
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.Windows

/-! # The auxiliary probe maps of mixed heights

Cases (b) and (c) of §3 of `docs/Nondegeneracy/ProbeWindowInverse.md`, (8)–(13) there. In
case (b) (`k ≥ 0`, `H = h - k < 0`, `d = -H`) the auxiliary map `X ⊕ Oᵈ ⟶ Y ⊕ Oᵏ` has corner
`s`, columns `-(u ≫ yᵗ)` (`t < d`), rows `c_r • (x^{-r-1} ≫ v)` (`r < k`, `c_r = q^(r+1)`)
and the identity block `g_t ↦ ρ_t` (`t < min d k`). In case (c) (`k = -a < 0`, `H ≥ 0`,
`d = H`) the auxiliary map `X ⊕ Oᵃ ⟶ Y ⊕ Oᵈ` has corner `s`, columns
`d_s • (u ≫ y^{-s-1})` (`s < a`, `d_s = q^(s+2)`), rows `xᵗ ≫ v` (`t < d`) and the identity
block `z_t ↦ f_t` (`t < min a d`).

Each is invertible as soon as the relevant probe window is
(`ProbeWindow.isIso_caseB_of_nonneg`, `ProbeWindow.isIso_caseB_of_neg`,
`ProbeWindow.isIso_caseC_of_nonneg`, `ProbeWindow.isIso_caseC_of_neg`). The proof eliminates
the identity block (`ProbeWindow.isIso_gMap_of_isCapInverse`,
`ProbeWindow.isIso_gMap_of_isCupInverse`); by the window identities (4) the remaining
window is the probe window, or its shift (5), (6), conjugated by probe-dot powers
(`ProbeWindow.IsCapInverse.conj`, `ProbeWindow.IsCupInverse.conj`) with its rows or columns
reordered and multiplied by units.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {X Y O : C}

/-- Conjugating a cap window by isomorphisms `f`, `t` and a unit `c` preserves entrywise
inverses. -/
theorem IsCapInverse.conj {X' Y' : C} {h : ℕ} {s : X ⟶ Y} {w : Fin h → (X ⟶ O)} {j : Y ⟶ X}
    {A : Fin h → (O ⟶ X)} (H : IsCapInverse s w j A) (f : X' ≅ X) (t : Y ≅ Y') (c : ℤ)
    (hc : c * c = 1) :
    IsCapInverse (c • (f.hom ≫ s ≫ t.hom)) (fun n => f.hom ≫ w n)
      (c • (t.inv ≫ j ≫ f.inv)) (fun n => A n ≫ f.inv) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨?_, fun n => ?_, fun m => ?_, fun n m => ?_, ?_⟩
  · simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hc, one_smul,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% h1, Iso.inv_hom_id]
  · simp only [Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (h2 n), Limits.zero_comp, smul_zero]
  · simp only [Preadditive.zsmul_comp, Category.assoc, Iso.inv_hom_id_assoc]
    rw [h3, Limits.comp_zero, smul_zero]
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact h4 n m
  · simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hc, one_smul,
      Category.assoc, Iso.hom_inv_id_assoc]
    have := congrArg (fun g => f.hom ≫ g ≫ f.inv) h5
    simpa only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
      Preadditive.comp_sum, Category.assoc, Category.id_comp, Iso.hom_inv_id] using this

/-- Conjugating a cup window by isomorphisms `f`, `t` and a unit `c` preserves entrywise
inverses. -/
theorem IsCupInverse.conj {X' Y' : C} {h : ℕ} {s : X ⟶ Y} {w : Fin h → (O ⟶ Y)} {j : Y ⟶ X}
    {D : Fin h → (Y ⟶ O)} (H : IsCupInverse s w j D) (f : X' ≅ X) (t : Y ≅ Y') (c : ℤ)
    (hc : c * c = 1) :
    IsCupInverse (c • (f.hom ≫ s ≫ t.hom)) (fun n => w n ≫ t.hom)
      (c • (t.inv ≫ j ≫ f.inv)) (fun n => t.inv ≫ D n) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨?_, fun n => ?_, fun m => ?_, fun m n => ?_, ?_⟩
  · simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hc, one_smul,
      Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% h1, Iso.hom_inv_id]
  · simp only [Preadditive.zsmul_comp, Category.assoc, Iso.hom_inv_id_assoc]
    rw [h2 n, Limits.comp_zero, smul_zero]
  · simp only [Preadditive.comp_zsmul, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% (h3 m), Limits.zero_comp, smul_zero]
  · simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact h4 m n
  · simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hc, one_smul,
      Category.assoc, Iso.inv_hom_id_assoc]
    have := congrArg (fun g => t.inv ≫ g ≫ t.hom) h5
    simpa only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
      Preadditive.comp_sum, Category.assoc, Category.id_comp, Iso.inv_hom_id] using this

omit [Preadditive C] in
private lemma zhom_comp {Z : C} (a : Aut Z) (m n : ℤ) :
    (a ^ m).hom ≫ (a ^ n).hom = (a ^ (m + n)).hom := by
  rw [add_comm, zpow_add, Aut.Aut_mul_def]; rfl

omit [Preadditive C] in
private lemma zhom_comp_assoc {Z W : C} (a : Aut Z) (m n : ℤ) (g : Z ⟶ W) :
    (a ^ m).hom ≫ (a ^ n).hom ≫ g = (a ^ (m + n)).hom ≫ g := by
  rw [← Category.assoc, zhom_comp]

omit [Preadditive C] in
private lemma inv_pow_hom {Z : C} (a : Aut Z) (r : ℕ) : (a⁻¹ ^ r).hom = (a ^ (-(r : ℤ))).hom := by
  rw [zpow_neg, zpow_natCast, inv_pow]

omit [Preadditive C] in
private lemma pow_hom {Z : C} (a : Aut Z) (r : ℕ) : (a ^ r).hom = (a ^ (r : ℤ)).hom := by
  rw [zpow_natCast]

private lemma pow_mul_self {q : ℤ} (hq : q * q = 1) (n : ℕ) : q ^ n * q ^ n = 1 := by
  rw [← mul_pow, hq, one_pow]

/-- **Case (b), `h ≥ 0`**, (8)–(9) of `ProbeWindowInverse.md`: for `d, h ≥ 0` (`k = d + h`), if
the cap window `[s; xⁿ ≫ v]_{n < h}` is invertible, so is the auxiliary map
`X ⊕ Oᵈ ⟶ Y ⊕ Oᵏ` of (8). -/
theorem isIso_caseB_of_nonneg (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O)
    (u : O ⟶ Y) (q : ℤ) (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u)
    {d h : ℕ} (h0 : ∃ j A, IsCapInverse s (fun n : Fin h => (x ^ (n : ℤ)).hom ≫ v) j A) :
    IsIso (gMap s (fun t : Fin d => -(u ≫ (y ^ (t : ℤ)).hom))
      (fun r : Fin (d + h) => q ^ ((r : ℕ) + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v))
      (fun t r => if (t : ℕ) = r then 𝟙 O else 0)) := by
  obtain ⟨j, A, H⟩ := exists_isCapInverse_shift s x y v u q hq hslide le_rfl h0
  have H' := (H.reindex Fin.revPerm (fun m : Fin h => q ^ (d + (m : ℕ) + 1))
    (fun m => pow_mul_self hq _)).conj (x ^ (-(d : ℤ))) (y ^ (d : ℤ)) (q ^ d) (pow_mul_self hq d)
  refine isIso_gMap_of_reindex_target _ _ _ _ finSumFinEquiv ?_
  rw [gMap_congr rfl (fun _ => rfl) (fun _ => rfl)
    (E' := fun t r => if r = Sum.inl t then 𝟙 O else 0) (fun t r => by
      rcases r with r | n
      · simp [Fin.ext_iff, eq_comm]
      · have := t.isLt
        simp [show (t : ℕ) ≠ d + n by omega])]
  apply isIso_gMap_of_isCapInverse
  convert H' using 1
  · have W := window_neg s x y v u q hq hslide d
    rw [← Fin.sum_univ_eq_sum_range
      (fun r => q ^ (r + 1) • ((x⁻¹ ^ (r + 1)).hom ≫ v ≫ u ≫ (y ^ r).hom))] at W
    simp only [inv_pow_hom] at W
    simp only [pow_hom, Nat.cast_add, Nat.cast_one, neg_add'] at W
    rw [← W]
    simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, Preadditive.comp_neg,
      Finset.sum_neg_distrib, sub_neg_eq_add, Preadditive.zsmul_comp, Category.assoc]
  · funext n
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, Preadditive.comp_zsmul]
    rw [zhom_comp_assoc, Fin.revPerm_apply, Fin.val_rev]
    congr 4
    have := n.isLt
    push_cast [Nat.cast_sub (show (n : ℕ) + 1 ≤ h by omega)]
    ring

/-- **Case (b), `h < 0`**, (8), (10) of `ProbeWindowInverse.md`: for `k ≥ 0`, `b = -h > 0`
(`d = k + b`), if the cup window `[s, u ≫ yⁿ]_{n < b}` is invertible, so is the auxiliary map
`X ⊕ Oᵈ ⟶ Y ⊕ Oᵏ` of (8). -/
theorem isIso_caseB_of_neg (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O)
    (u : O ⟶ Y) (q : ℤ) (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u)
    {k b : ℕ} (h0 : ∃ j D, IsCupInverse s (fun n : Fin b => u ≫ (y ^ (n : ℤ)).hom) j D) :
    IsIso (gMap s (fun t : Fin (k + b) => -(u ≫ (y ^ (t : ℤ)).hom))
      (fun r : Fin k => q ^ ((r : ℕ) + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v))
      (fun t r => if (t : ℕ) = r then 𝟙 O else 0)) := by
  obtain ⟨j, D, H⟩ := h0
  have H' := (H.conj (x ^ (-(k : ℤ))) (y ^ (k : ℤ)) (q ^ k) (pow_mul_self hq k)).reindex
    (Equiv.refl _) (fun _ => -1) (fun _ => by norm_num)
  refine isIso_gMap_of_reindex_source _ _ _ _ finSumFinEquiv ?_
  rw [gMap_congr rfl (fun _ => rfl) (fun _ => rfl)
    (E' := fun t r => if t = Sum.inl r then 𝟙 O else 0) (fun t r => by
      rcases t with t | n
      · simp [Fin.ext_iff]
      · have := r.isLt
        simp [show k + (n : ℕ) ≠ r by omega])]
  apply isIso_gMap_of_isCupInverse
  convert H' using 1
  · have W := window_neg s x y v u q hq hslide k
    rw [← Fin.sum_univ_eq_sum_range
      (fun r => q ^ (r + 1) • ((x⁻¹ ^ (r + 1)).hom ≫ v ≫ u ≫ (y ^ r).hom))] at W
    simp only [inv_pow_hom] at W
    simp only [pow_hom, Nat.cast_add, Nat.cast_one, neg_add'] at W
    rw [← W]
    simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, Preadditive.comp_neg,
      Finset.sum_neg_distrib, sub_neg_eq_add, Preadditive.zsmul_comp, Category.assoc]
  · funext n
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, Equiv.refl_apply, Category.assoc,
      zhom_comp, neg_smul, one_smul]
    congr 4
    push_cast
    ring

/-- **Case (c), `h ≥ 0`**, (11)–(12) of `ProbeWindowInverse.md`: for `a = -k > 0` and `h ≥ 0`
(`d = a + h`), if the cap window `[s; xⁿ ≫ v]_{n < h}` is invertible, so is the auxiliary map
`X ⊕ Oᵃ ⟶ Y ⊕ Oᵈ` of (11). -/
theorem isIso_caseC_of_nonneg (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O)
    (u : O ⟶ Y) (q : ℤ) (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u)
    {a h : ℕ} (h0 : ∃ j A, IsCapInverse s (fun n : Fin h => (x ^ (n : ℤ)).hom ≫ v) j A) :
    IsIso (gMap s (fun t : Fin a => q ^ ((t : ℕ) + 2) • (u ≫ (y ^ (-(t : ℤ) - 1)).hom))
      (fun r : Fin (a + h) => (x ^ (r : ℤ)).hom ≫ v)
      (fun t r => if (t : ℕ) = r then 𝟙 O else 0)) := by
  obtain ⟨j, A, H⟩ := h0
  have H' := H.conj (x ^ (a : ℤ)) (y ^ (-(a : ℤ))) (q ^ a) (pow_mul_self hq a)
  refine isIso_gMap_of_reindex_target _ _ _ _ finSumFinEquiv ?_
  rw [gMap_congr rfl (fun _ => rfl) (fun _ => rfl)
    (E' := fun t r => if r = Sum.inl t then 𝟙 O else 0) (fun t r => by
      rcases r with r | n
      · simp [Fin.ext_iff, eq_comm]
      · have := t.isLt
        simp [show (t : ℕ) ≠ a + n by omega])]
  apply isIso_gMap_of_isCapInverse
  convert H' using 1
  · have W := window_pos s x y v u q hq hslide a
    rw [← Fin.sum_univ_eq_sum_range
      (fun r => q ^ (r + 2) • ((x ^ r).hom ≫ v ≫ u ≫ (y⁻¹ ^ (r + 1)).hom))] at W
    simp only [inv_pow_hom] at W
    simp only [pow_hom, Nat.cast_add, Nat.cast_one, neg_add'] at W
    rw [← W]
    simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, Preadditive.comp_zsmul,
      Category.assoc]
  · funext n
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, zhom_comp_assoc]
    congr 3

/-- **Case (c), `h < 0`**, (11), (13) of `ProbeWindowInverse.md`: for `d ≥ 0`, `b = -h > 0`
(`a = -k = d + b`), if the cup window `[s, u ≫ yⁿ]_{n < b}` is invertible, so is the auxiliary
map `X ⊕ Oᵃ ⟶ Y ⊕ Oᵈ` of (11). -/
theorem isIso_caseC_of_neg (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O)
    (u : O ⟶ Y) (q : ℤ) (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u)
    {d b : ℕ} (h0 : ∃ j D, IsCupInverse s (fun n : Fin b => u ≫ (y ^ (n : ℤ)).hom) j D) :
    IsIso (gMap s (fun t : Fin (d + b) => q ^ ((t : ℕ) + 2) • (u ≫ (y ^ (-(t : ℤ) - 1)).hom))
      (fun r : Fin d => (x ^ (r : ℤ)).hom ≫ v)
      (fun t r => if (t : ℕ) = r then 𝟙 O else 0)) := by
  obtain ⟨j, D, H⟩ := exists_isCupInverse_shift s x y v u q hq hslide le_rfl h0
  have H' := (H.reindex Fin.revPerm (fun m : Fin b => q ^ (d + (m : ℕ) + 2))
    (fun m => pow_mul_self hq _)).conj (x ^ (d : ℤ)) (y ^ (-(d : ℤ))) (q ^ d)
    (pow_mul_self hq d)
  refine isIso_gMap_of_reindex_source _ _ _ _ finSumFinEquiv ?_
  rw [gMap_congr rfl (fun _ => rfl) (fun _ => rfl)
    (E' := fun t r => if t = Sum.inl r then 𝟙 O else 0) (fun t r => by
      rcases t with t | n
      · simp [Fin.ext_iff]
      · have := r.isLt
        simp [show d + (n : ℕ) ≠ r by omega])]
  apply isIso_gMap_of_isCupInverse
  convert H' using 1
  · have W := window_pos s x y v u q hq hslide d
    rw [← Fin.sum_univ_eq_sum_range
      (fun r => q ^ (r + 2) • ((x ^ r).hom ≫ v ≫ u ≫ (y⁻¹ ^ (r + 1)).hom))] at W
    simp only [inv_pow_hom] at W
    simp only [pow_hom, Nat.cast_add, Nat.cast_one, neg_add'] at W
    rw [← W]
    simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, Preadditive.comp_zsmul,
      Category.assoc]
  · funext n
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, Preadditive.zsmul_comp,
      Category.assoc, zhom_comp, Fin.revPerm_apply, Fin.val_rev]
    congr 4
    have := n.isLt
    push_cast [Nat.cast_sub (show (n : ℕ) + 1 ≤ b by omega)]
    ring

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
